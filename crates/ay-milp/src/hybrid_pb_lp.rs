// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact binary-master / continuous-LP decomposition.
//!
//! This route owns the common fixed-charge shape in which every integral
//! column is Boolean and fixing the Boolean columns leaves a continuous LP.  A
//! compact PB master contains the original pure-Boolean rows and the discrete
//! part of the objective.  Each master candidate is checked against the full
//! LP.  An infeasible subproblem produces an exact Farkas certificate and then
//! either:
//!
//! * a globally valid [`CertifiedRow`] obtained by removing the temporary
//!   master-bound facts from that certificate, or
//! * an exact Boolean no-good, licensed by the same certificate against the
//!   fixed assignment, when the projected row does not fit the PB integer
//!   coefficient envelope.
//!
//! A continuous objective is handled by exact generalized Benders cuts.  The
//! fixed LP supplies a verified optimality certificate.  Temporary assignment
//! bounds are removed from its multiplier list, and the remaining combination
//! must independently verify against the original model as a global dual row.
//! That row and the exact incumbent induce a strict PB constraint containing
//! precisely the assignments that can still improve the incumbent.  When the
//! incumbent improves, every retained optimality cut is strengthened before
//! search continues.
//!
//! The loop is fail-closed at every boundary.  A feasible candidate becomes a
//! result only after an exact point and objective check against the original
//! model.  An optimum is returned only after the PB master proves that no
//! assignment can improve the retained exact incumbent.  Master infeasibility
//! is accepted only after every accumulated cut license is rechecked.  An
//! original-model infeasibility verdict additionally requires a bounded exact
//! decision-DAG refutation of the reconstructed final PB master; a bare PB
//! portfolio `UNSAT` status is never exported as proof.

use std::io::{self, Write};
use std::mem::size_of;
use std::sync::atomic::AtomicBool;
use std::time::{Duration, Instant};

use ay_lra::rational::Rational;
use ay_pb_core::portfolio::{solve_decision_portfolio, solve_optimization_portfolio};
use ay_pb_core::{
    encode_multi_row_bdd_infeasibility_certificate_json,
    generate_multi_row_bdd_infeasibility_certificate_interruptible, verify_all_constraints,
    verify_multi_row_bdd_infeasibility_certificate_interruptible,
    MultiRowBddInfeasibilityCertificate, PbConstraint, PbInstance, PbLit, PbObjective, PbRel,
    PbStatus, PbTerm,
};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

use crate::cert::{
    BoundSide, CertifiedRow, FactRef, FarkasCertificate, Multiplier, OptimalityCertificate,
};
use crate::certify::certify_bounded_by;
use crate::exact::{Budget, ExactLp, LpFeasibility, LpOptimum};
use crate::model::{exact, Col, ColKind, Model, Row, Sense};
use crate::pb_translate::{translate, PbObjectivePlan, PbRoutePlan};
use crate::simplex::{Candidate, FloatLp, NbBound, SimplexStatus};
use crate::tree_cert::exact_farkas_from_float_ray;

/// Bound the amount of replay evidence and guard against a pathological
/// one-assignment-at-a-time decomposition.  Hitting the cap is a decline, never
/// an incomplete infeasibility/optimality claim.
const MAX_BENDERS_CUTS: usize = 8_192;

/// Hard envelope for replay evidence retained by one decomposition attempt.
///
/// The estimate includes both PB copies of every learned row (the exact plan
/// and the core instance), assignment licenses, exact row coefficients, and
/// exact Farkas multipliers.  The count caps are independent backstops for
/// unusually small objects.  Reaching any cap is a fail-closed route decline.
const MAX_RETAINED_CUT_BYTES: usize = 64 * 1024 * 1024;
const MAX_RETAINED_ASSIGNMENT_VALUES: usize = 16 * 1024 * 1024;
const MAX_RETAINED_PB_TERMS: usize = 2 * 1024 * 1024;
const MAX_RETAINED_EXACT_MULTIPLIERS: usize = 1024 * 1024;

/// Stable format tag for the outer hybrid cut-ledger/refutation artifact.
pub(crate) const HYBRID_PB_LP_INFEASIBILITY_CERTIFICATE_FORMAT: &str =
    "ay.hybrid-pb-lp-infeasible.v1";

/// The outer JSON envelope is independently bounded.  The nested PB
/// refutation has its own, stricter codec limit in `ay-pb-core`.
const MAX_HYBRID_CERTIFICATE_JSON_BYTES: u64 = 64 << 20;

/// A conclusive result from the exact hybrid reduction.
#[cfg(test)]
pub(crate) enum HybridPbLpDecision {
    Feasible,
    Infeasible,
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
    },
}

/// A hybrid result that retains proof data for an infeasible verdict.
///
/// Proof-requiring callers use this type so they cannot accidentally discard
/// the hybrid cut ledger or the final PB refutation.
pub(crate) enum CertifiedHybridPbLpDecision {
    Feasible {
        model_values: Vec<BigRational>,
        incumbent_only: bool,
    },
    Infeasible(HybridPbLpInfeasibilityCertificate),
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
    },
}

/// Independently replayable proof that the binary-master/continuous-recourse
/// decomposition is infeasible.
///
/// The checker trusts neither a stored master nor stored learned PB rows.
/// It rebuilds both from the original model and these exact licenses, then
/// verifies `master_refutation` against that rebuilt final master.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HybridPbLpInfeasibilityCertificate {
    pub(crate) format: String,
    pub(crate) cuts: Vec<HybridPbLpInfeasibilityCut>,
    pub(crate) master_refutation: MultiRowBddInfeasibilityCertificate,
}

/// One exact license in the order it was appended to the PB master.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(crate) enum HybridPbLpInfeasibilityCut {
    /// A globally valid projected Farkas row.  Its PB restriction is rebuilt
    /// from the exact row; no stored coefficient vector is trusted.
    Certified {
        assignment: Vec<bool>,
        row: HybridCertifiedRow,
    },
    /// A single Boolean assignment excluded by an exact Farkas contradiction
    /// under precisely that assignment's fixed column bounds.
    NoGood {
        assignment: Vec<bool>,
        farkas: HybridFarkas,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct HybridCertifiedRow {
    coeffs: Vec<(u32, HybridRational)>,
    lb: HybridRational,
    multipliers: Vec<HybridMultiplier>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct HybridFarkas {
    multipliers: Vec<HybridMultiplier>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct HybridMultiplier {
    fact: HybridFactRef,
    coeff: HybridRational,
}

/// Panic-free rational wire form.  `num-rational`'s in-memory invariant is
/// restored only after explicitly checking a positive, canonical denominator.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct HybridRational {
    #[serde(with = "hybrid_decimal_bigint")]
    numerator: BigInt,
    #[serde(with = "hybrid_decimal_bigint")]
    denominator: BigInt,
}

/// Stable, language-neutral decimal encoding for artifact big integers.
/// This deliberately avoids `num-bigint`'s serde limb representation, whose
/// layout is crate-version-coupled and unsuitable for a durable certificate.
mod hybrid_decimal_bigint {
    use num_bigint::BigInt;
    use serde::{Deserialize, Deserializer, Serializer};

    pub(super) fn serialize<S>(value: &BigInt, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&value.to_string())
    }

    pub(super) fn deserialize<'de, D>(deserializer: D) -> Result<BigInt, D::Error>
    where
        D: Deserializer<'de>,
    {
        let encoded = String::deserialize(deserializer)?;
        let value = encoded
            .parse::<BigInt>()
            .map_err(serde::de::Error::custom)?;
        if value.to_string() != encoded {
            return Err(serde::de::Error::custom(
                "big integer is not canonical decimal",
            ));
        }
        Ok(value)
    }
}

/// A closed wire representation avoids depending on serde details of the
/// public, non-exhaustive model fact enums.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum HybridFactRef {
    RowLower { row: u32 },
    RowUpper { row: u32 },
    ColLower { col: u32 },
    ColUpper { col: u32 },
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum HybridPbLpCertificateCodecError {
    #[error("hybrid PB/LP certificate exceeds the {limit}-byte encoded limit")]
    Oversized { limit: u64 },
    #[error("malformed hybrid PB/LP certificate: {0}")]
    Malformed(#[source] serde_json::Error),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub(crate) enum HybridPbLpCertificateVerificationError {
    #[error("hybrid certificate verification was interrupted")]
    Interrupted,
    #[error("model is not an admissible binary-master/continuous-recourse decomposition")]
    UnsupportedModel,
    #[error("hybrid cut ledger is malformed or exceeds its resource envelope")]
    InvalidCutLedger,
    #[error("final PB master refutation failed independent replay")]
    MasterRefutationRejected,
    #[error("hybrid certificate cannot be represented by the bounded codec")]
    SerializationLimit,
}

/// Try the hybrid route.  `None` is a structural decline, timeout, resource
/// stop, unsupported PB integer range, or a result that failed an exact check.
#[cfg(test)]
pub(crate) fn try_solve(model: &Model, deadline: Option<Instant>) -> Option<HybridPbLpDecision> {
    try_solve_interruptible(model, deadline, || false)
}

#[cfg(test)]
pub(crate) fn try_solve_interruptible<F>(
    model: &Model,
    deadline: Option<Instant>,
    should_stop: F,
) -> Option<HybridPbLpDecision>
where
    F: FnMut() -> bool,
{
    try_solve_certified_interruptible(model, deadline, should_stop).map(drop_hybrid_certificate)
}

/// Run the hybrid route while retaining independently replayable
/// infeasibility evidence.  Unlike [`try_solve_interruptible`], an infeasible
/// result is impossible unless the exact cut ledger and final PB refutation
/// both verify and fit their serialization envelopes.
pub(crate) fn try_solve_certified(
    model: &Model,
    deadline: Option<Instant>,
) -> Option<CertifiedHybridPbLpDecision> {
    try_solve_certified_interruptible(model, deadline, || false)
}

pub(crate) fn try_solve_certified_interruptible<F>(
    model: &Model,
    deadline: Option<Instant>,
    mut should_stop: F,
) -> Option<CertifiedHybridPbLpDecision>
where
    F: FnMut() -> bool,
{
    let started = Instant::now();
    if stopped(deadline, &mut should_stop) {
        return None;
    }
    let decomposition = Decomposition::admit(model, deadline, &mut should_stop)?;
    if stopped(deadline, &mut should_stop) {
        return None;
    }
    // Translate the immutable initial master exactly once.  Learned Benders
    // rows are already exact PB inequalities, so rebuilding and retranslating
    // a growing `Model` on every iteration would only duplicate work and
    // memory without adding an independent soundness check.
    let plan = translate(&decomposition.master, deadline).ok()?;
    if plan.num_vars as usize != decomposition.master_to_original.len() {
        return None;
    }
    let instance = core_instance(&plan, deadline, &mut should_stop)?;
    let mut master = MasterState { plan, instance };
    let mut subproblem = ContinuousSubproblem::new(model, deadline, &mut should_stop)?;
    let mut cuts = RetainedCuts::new(
        CutResourceLimits::production(),
        master.plan.constraints.len(),
    );
    let mut incumbent: Option<(BigRational, Vec<BigRational>)> = None;

    for iteration in 0..=MAX_BENDERS_CUTS {
        if stopped(deadline, &mut should_stop) {
            return None;
        }
        let master_result = solve_master(
            &master.instance,
            master.instance.objective.as_ref(),
            &master.plan,
            deadline,
            &mut should_stop,
        )?;

        match master_result {
            MasterSolve::Infeasible => {
                if !cuts.verify_all(model, &decomposition, &master, deadline, &mut should_stop) {
                    return None;
                }
                if let Some((value, model_values)) = incumbent {
                    if model.check_point(&model_values).is_err()
                        || model.objective_value_at(&model_values) != value
                    {
                        return None;
                    }
                    trace_result(&decomposition, iteration, "OPTIMAL", started.elapsed());
                    return Some(CertifiedHybridPbLpDecision::Optimal {
                        value,
                        model_values,
                    });
                }
                let certificate = build_infeasibility_certificate(
                    model,
                    &decomposition,
                    &master,
                    &cuts,
                    deadline,
                    &mut should_stop,
                )?;
                trace_result(&decomposition, iteration, "INFEASIBLE", started.elapsed());
                return Some(CertifiedHybridPbLpDecision::Infeasible(certificate));
            }
            MasterSolve::Candidate {
                assignment,
                claimed_objective,
                proven_optimal,
            } => match subproblem.check(
                model,
                &decomposition,
                &assignment,
                deadline,
                &mut should_stop,
            )? {
                SubproblemDecision::Feasible(model_values) => {
                    let value = model.objective_value_at(&model_values);
                    if let Some(claimed) = claimed_objective {
                        let mapped = master.plan.objective.as_ref()?.map.model_value(claimed);
                        if value != mapped {
                            return None;
                        }
                    }
                    if model.has_objective() && proven_optimal {
                        trace_result(&decomposition, iteration, "OPTIMAL", started.elapsed());
                        return Some(CertifiedHybridPbLpDecision::Optimal {
                            value,
                            model_values,
                        });
                    }
                    trace_result(&decomposition, iteration, "FEASIBLE", started.elapsed());
                    return Some(CertifiedHybridPbLpDecision::Feasible {
                        model_values,
                        incumbent_only: model.has_objective(),
                    });
                }
                SubproblemDecision::Optimal {
                    value,
                    model_values,
                    dual_row,
                } => {
                    if !decomposition.has_continuous_objective
                        || model.check_point(&model_values).is_err()
                        || model.objective_value_at(&model_values) != value
                    {
                        return None;
                    }
                    let improves = incumbent
                        .as_ref()
                        .is_none_or(|(best, _)| objective_better(model.sense(), &value, best));
                    if improves {
                        cuts.strengthen_optimality(
                            model,
                            &decomposition,
                            &mut master,
                            &value,
                            deadline,
                            &mut should_stop,
                        )?;
                        incumbent = Some((value.clone(), model_values));
                    }
                    if iteration == MAX_BENDERS_CUTS {
                        return None;
                    }
                    decomposition.add_optimality_cut(
                        model,
                        &assignment,
                        dual_row,
                        incumbent.as_ref()?.0.clone(),
                        &mut master,
                        &mut cuts,
                        deadline,
                        &mut should_stop,
                    )?;
                }
                SubproblemDecision::Infeasible(farkas) => {
                    if iteration == MAX_BENDERS_CUTS {
                        return None;
                    }
                    decomposition.add_cut(
                        model,
                        &assignment,
                        farkas,
                        &mut master,
                        &mut cuts,
                        deadline,
                        &mut should_stop,
                    )?;
                }
            },
        }
    }
    None
}

#[cfg(test)]
fn drop_hybrid_certificate(decision: CertifiedHybridPbLpDecision) -> HybridPbLpDecision {
    match decision {
        CertifiedHybridPbLpDecision::Feasible { .. } => HybridPbLpDecision::Feasible,
        CertifiedHybridPbLpDecision::Infeasible(_) => HybridPbLpDecision::Infeasible,
        CertifiedHybridPbLpDecision::Optimal {
            value,
            model_values,
        } => HybridPbLpDecision::Optimal {
            value,
            model_values,
        },
    }
}

fn build_infeasibility_certificate<F>(
    original: &Model,
    decomposition: &Decomposition,
    master: &MasterState,
    cuts: &RetainedCuts,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<HybridPbLpInfeasibilityCertificate>
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) || cuts.licenses.len() > MAX_BENDERS_CUTS {
        return None;
    }
    let mut artifact_cuts = Vec::with_capacity(cuts.licenses.len());
    for (index, license) in cuts.licenses.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        // An optimality restriction proves only that no assignment improves a
        // retained incumbent.  It must never appear in an original-model
        // infeasibility proof.
        artifact_cuts.push(HybridPbLpInfeasibilityCut::from_license(license)?);
    }
    let master_refutation =
        generate_multi_row_bdd_infeasibility_certificate_interruptible(&master.instance, || {
            stopped(deadline, should_stop)
        })
        .ok()??;
    if stopped(deadline, should_stop) {
        return None;
    }
    let certificate = HybridPbLpInfeasibilityCertificate {
        format: HYBRID_PB_LP_INFEASIBILITY_CERTIFICATE_FORMAT.to_owned(),
        cuts: artifact_cuts,
        master_refutation,
    };
    // Generation and replay intentionally cross the same public typed API as
    // an external checker.  This catches any disagreement in decomposition,
    // cut reconstruction, PB normalization, or final-master identity before
    // the route can return an infeasible verdict.
    verify_hybrid_pb_lp_infeasibility_certificate_interruptible(
        original,
        &certificate,
        deadline,
        should_stop,
    )
    .ok()?;
    // Verifiability in memory is not enough for a proof-requiring route: the
    // artifact must fit the bounded wire codec that certificate I/O uses.
    encode_hybrid_pb_lp_infeasibility_certificate_json(&certificate).ok()?;
    // Keep the already-live decomposition in the function contract explicit;
    // the independent verifier above rebuilt it rather than trusting it.
    if decomposition.master_to_original.len() != master.plan.num_vars as usize {
        return None;
    }
    Some(certificate)
}

/// Independently rebuild and replay a hybrid infeasibility artifact.
pub(crate) fn verify_hybrid_pb_lp_infeasibility_certificate(
    original: &Model,
    certificate: &HybridPbLpInfeasibilityCertificate,
) -> Result<(), HybridPbLpCertificateVerificationError> {
    verify_hybrid_pb_lp_infeasibility_certificate_interruptible(
        original,
        certificate,
        None,
        &mut || false,
    )
}

pub(crate) fn verify_hybrid_pb_lp_infeasibility_certificate_interruptible<F>(
    original: &Model,
    certificate: &HybridPbLpInfeasibilityCertificate,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Result<(), HybridPbLpCertificateVerificationError>
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) {
        return Err(HybridPbLpCertificateVerificationError::Interrupted);
    }
    if certificate.format != HYBRID_PB_LP_INFEASIBILITY_CERTIFICATE_FORMAT
        || certificate.cuts.len() > MAX_BENDERS_CUTS
    {
        return Err(HybridPbLpCertificateVerificationError::InvalidCutLedger);
    }
    encode_hybrid_pb_lp_infeasibility_certificate_json(certificate)
        .map_err(|_| HybridPbLpCertificateVerificationError::SerializationLimit)?;
    encode_multi_row_bdd_infeasibility_certificate_json(&certificate.master_refutation)
        .map_err(|_| HybridPbLpCertificateVerificationError::SerializationLimit)?;

    let decomposition = Decomposition::admit(original, deadline, should_stop)
        .ok_or_else(|| verification_decline(deadline, should_stop))?;
    let plan = translate(&decomposition.master, deadline)
        .map_err(|_| verification_decline(deadline, should_stop))?;
    if plan.num_vars as usize != decomposition.master_to_original.len() {
        return Err(HybridPbLpCertificateVerificationError::UnsupportedModel);
    }
    let instance = core_instance(&plan, deadline, should_stop)
        .ok_or_else(|| verification_decline(deadline, should_stop))?;
    let mut master = MasterState { plan, instance };
    let mut retained = RetainedCuts::new(
        CutResourceLimits::production(),
        master.plan.constraints.len(),
    );

    for (index, artifact_cut) in certificate.cuts.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridPbLpCertificateVerificationError::Interrupted);
        }
        let license = artifact_cut
            .to_license()
            .ok_or(HybridPbLpCertificateVerificationError::InvalidCutLedger)?;
        let restriction = match &license {
            CutLicense::Certified { row, .. } => {
                certified_cut_inequality(&decomposition, row, deadline, should_stop)
            }
            CutLicense::NoGood { assignment, .. } => {
                no_good_inequality(master.plan.num_vars, assignment, deadline, should_stop)
            }
            CutLicense::Optimality { .. } => None,
        }
        .ok_or_else(|| verification_decline(deadline, should_stop))?;
        if !license.verify(original, &decomposition, deadline, should_stop)
            || !license.matches_restriction(
                original,
                &decomposition,
                &restriction,
                deadline,
                should_stop,
            )
        {
            return Err(if stopped(deadline, should_stop) {
                HybridPbLpCertificateVerificationError::Interrupted
            } else {
                HybridPbLpCertificateVerificationError::InvalidCutLedger
            });
        }
        retained
            .retain(&mut master, license, restriction, deadline, should_stop)
            .ok_or_else(|| verification_decline(deadline, should_stop))?;
    }
    if !retained.verify_all(original, &decomposition, &master, deadline, should_stop) {
        return Err(if stopped(deadline, should_stop) {
            HybridPbLpCertificateVerificationError::Interrupted
        } else {
            HybridPbLpCertificateVerificationError::InvalidCutLedger
        });
    }

    verify_multi_row_bdd_infeasibility_certificate_interruptible(
        &master.instance,
        &certificate.master_refutation,
        || stopped(deadline, should_stop),
    )
    .map_err(|_| {
        if stopped(deadline, should_stop) {
            HybridPbLpCertificateVerificationError::Interrupted
        } else {
            HybridPbLpCertificateVerificationError::MasterRefutationRejected
        }
    })
}

fn verification_decline<F>(
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> HybridPbLpCertificateVerificationError
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) {
        HybridPbLpCertificateVerificationError::Interrupted
    } else {
        HybridPbLpCertificateVerificationError::InvalidCutLedger
    }
}

/// Encode an artifact without allowing serde to grow an unbounded buffer.
pub(crate) fn encode_hybrid_pb_lp_infeasibility_certificate_json(
    certificate: &HybridPbLpInfeasibilityCertificate,
) -> Result<Vec<u8>, HybridPbLpCertificateCodecError> {
    encode_hybrid_pb_lp_infeasibility_certificate_json_with_limit(
        certificate,
        MAX_HYBRID_CERTIFICATE_JSON_BYTES,
    )
}

fn encode_hybrid_pb_lp_infeasibility_certificate_json_with_limit(
    certificate: &HybridPbLpInfeasibilityCertificate,
    max_bytes: u64,
) -> Result<Vec<u8>, HybridPbLpCertificateCodecError> {
    let mut writer = BoundedHybridCertificateWriter::new(max_bytes);
    let result = serde_json::to_writer(&mut writer, certificate);
    if writer.exceeded {
        return Err(HybridPbLpCertificateCodecError::Oversized { limit: max_bytes });
    }
    result.map_err(HybridPbLpCertificateCodecError::Malformed)?;
    Ok(writer.bytes)
}

/// Decode only after applying the encoded-size cap.  Semantic and allocation
/// limits inside the artifact are checked by the independent verifier.
pub(crate) fn decode_hybrid_pb_lp_infeasibility_certificate_json(
    encoded: &[u8],
) -> Result<HybridPbLpInfeasibilityCertificate, HybridPbLpCertificateCodecError> {
    if u64::try_from(encoded.len()).unwrap_or(u64::MAX) > MAX_HYBRID_CERTIFICATE_JSON_BYTES {
        return Err(HybridPbLpCertificateCodecError::Oversized {
            limit: MAX_HYBRID_CERTIFICATE_JSON_BYTES,
        });
    }
    serde_json::from_slice(encoded).map_err(HybridPbLpCertificateCodecError::Malformed)
}

struct BoundedHybridCertificateWriter {
    bytes: Vec<u8>,
    max_bytes: u64,
    exceeded: bool,
}

impl BoundedHybridCertificateWriter {
    fn new(max_bytes: u64) -> Self {
        Self {
            bytes: Vec::new(),
            max_bytes,
            exceeded: false,
        }
    }
}

impl Write for BoundedHybridCertificateWriter {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        let length = u64::try_from(self.bytes.len())
            .unwrap_or(u64::MAX)
            .checked_add(u64::try_from(buffer.len()).unwrap_or(u64::MAX));
        if length.is_none_or(|length| length > self.max_bytes) {
            self.exceeded = true;
            return Err(io::Error::other("hybrid certificate size limit"));
        }
        self.bytes.extend_from_slice(buffer);
        Ok(buffer.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The compact PB master and its stable local/original column bijection.
struct Decomposition {
    master: Model,
    master_to_original: Vec<Col>,
    original_to_master: Vec<Option<Col>>,
    coupling_rows: usize,
    has_continuous_objective: bool,
}

impl Decomposition {
    /// Structurally admit a binary-master/continuous-subproblem model and copy
    /// every pure-master fact exactly into a compact model.
    fn admit<F>(model: &Model, deadline: Option<Instant>, should_stop: &mut F) -> Option<Self>
    where
        F: FnMut() -> bool,
    {
        model.validate().ok()?;
        let mut master = Model::new();
        let mut master_to_original = Vec::new();
        let mut original_to_master = vec![None; model.num_cols()];
        let mut continuous = 0usize;
        let mut has_continuous_objective = false;

        for j in 0..model.num_cols() {
            if j & 0x3ff == 0 && stopped(deadline, should_stop) {
                return None;
            }
            let original = Col(j as u32);
            match model.col_kind(original) {
                ColKind::Binary => {
                    let (lb, ub) = model.col_bounds(original);
                    // The compact PB translator intentionally accepts only
                    // finite domains contained in {0,1}; keep that contract
                    // explicit at this partial-projection boundary too.
                    if !lb.is_finite() || !ub.is_finite() || lb < 0.0 || ub > 1.0 {
                        return None;
                    }
                    let local = master.add_binary_col();
                    master.set_col_bounds(local, lb, ub);
                    original_to_master[j] = Some(local);
                    master_to_original.push(original);
                }
                ColKind::Continuous => {
                    continuous += 1;
                    let advice = model.obj_coeff(original);
                    if !model.obj_coeff_exact_at(j as u32, advice).is_zero() {
                        has_continuous_objective = true;
                    }
                }
                // General integers need a separate exact order/binary encoding;
                // silently relaxing one into a PB bit is forbidden.
                ColKind::Integer => return None,
            }
        }
        if master_to_original.is_empty() || continuous == 0 {
            return None;
        }

        let mut coupling_rows = 0usize;
        for r in 0..model.num_rows() {
            if r & 0x3ff == 0 && stopped(deadline, should_stop) {
                return None;
            }
            let (coeffs, lb, ub) = model.row(Row(r as u32));
            let mut local_terms = Vec::new();
            let mut has_continuous = false;
            for (term_index, &(column, advice)) in coeffs.iter().enumerate() {
                if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
                    return None;
                }
                let coefficient = model.row_coeff_exact(r, column, advice);
                if coefficient.is_zero() {
                    continue;
                }
                match original_to_master[column as usize] {
                    Some(local) => local_terms.push((local, advice, coefficient)),
                    None => has_continuous = true,
                }
            }
            if has_continuous {
                if !local_terms.is_empty() {
                    coupling_rows += 1;
                }
                continue;
            }
            append_copied_row(
                &mut master,
                model,
                r,
                lb,
                ub,
                &local_terms,
                deadline,
                should_stop,
            )?;
        }
        // A model with no row connecting the two blocks is better handled by
        // the already-existing independent PB and LP paths; admitting it here
        // would add machinery without doing a decomposition.
        if coupling_rows == 0 {
            return None;
        }

        if model.has_objective() {
            let mut objective = Vec::new();
            let mut exact_objective = Vec::new();
            for (local_index, &original) in master_to_original.iter().enumerate() {
                if local_index & 0x3ff == 0 && stopped(deadline, should_stop) {
                    return None;
                }
                let advice = model.obj_coeff(original);
                let coefficient = model.obj_coeff_exact_at(original.0, advice);
                if advice != 0.0 || !coefficient.is_zero() {
                    objective.push((Col(local_index as u32), advice));
                    exact_objective.push((local_index as u32, advice, coefficient));
                }
            }
            master.set_objective(&objective, model.sense());
            for (index, (column, advice, coefficient)) in exact_objective.into_iter().enumerate() {
                if index & 0x3ff == 0 && stopped(deadline, should_stop) {
                    return None;
                }
                if exact(advice).as_ref() != Some(&coefficient) {
                    master.record_inexact_obj_coeff(column, coefficient);
                }
            }
            master.set_objective_offset(model.objective_offset());
            let exact_offset = model.obj_offset_exact();
            if exact(model.objective_offset()).as_ref() != Some(&exact_offset) {
                master.record_inexact_obj_offset(exact_offset);
            }
        }

        Some(Self {
            master,
            master_to_original,
            original_to_master,
            coupling_rows,
            has_continuous_objective,
        })
    }

    fn add_cut<F>(
        &self,
        original: &Model,
        assignment: &[bool],
        farkas: FarkasCertificate,
        master: &mut MasterState,
        cuts: &mut RetainedCuts,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> Option<()>
    where
        F: FnMut() -> bool,
    {
        let fixed = self.fixed_model(original, assignment, deadline, should_stop)?;
        farkas.verify(&fixed).ok()?;
        if stopped(deadline, should_stop) {
            return None;
        }

        // Prefer the true Benders row.  Convert it directly to the compact PB
        // indices.  An i128-inexpressible projection has not mutated the live
        // master, so the exactly licensed no-good remains a safe fallback.
        if let Some(row) =
            project_farkas_row(original, self, assignment, &farkas, deadline, should_stop)
        {
            if let Some(inequality) = certified_cut_inequality(self, &row, deadline, should_stop) {
                let license = CutLicense::Certified {
                    assignment: assignment.to_vec(),
                    row,
                };
                if !license.verify(original, self, deadline, should_stop) {
                    return None;
                }
                if !license.matches_restriction(original, self, &inequality, deadline, should_stop)
                {
                    return None;
                }
                return cuts.retain(master, license, inequality, deadline, should_stop);
            }
            if stopped(deadline, should_stop) {
                return None;
            }
        }

        let inequality =
            no_good_inequality(master.plan.num_vars, assignment, deadline, should_stop)?;
        let license = CutLicense::NoGood {
            assignment: assignment.to_vec(),
            farkas,
        };
        if !license.verify(original, self, deadline, should_stop) {
            return None;
        }
        if !license.matches_restriction(original, self, &inequality, deadline, should_stop) {
            return None;
        }
        cuts.retain(master, license, inequality, deadline, should_stop)
    }

    fn add_optimality_cut<F>(
        &self,
        original: &Model,
        assignment: &[bool],
        row: CertifiedRow,
        incumbent: BigRational,
        master: &mut MasterState,
        cuts: &mut RetainedCuts,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> Option<()>
    where
        F: FnMut() -> bool,
    {
        let inequality =
            improvement_inequality(original, self, &row, &incumbent, deadline, should_stop)?;
        let license = CutLicense::Optimality {
            assignment: assignment.to_vec(),
            row,
            incumbent,
        };
        if !license.verify(original, self, deadline, should_stop)
            || !license.matches_restriction(original, self, &inequality, deadline, should_stop)
        {
            return None;
        }
        cuts.retain(master, license, inequality, deadline, should_stop)
    }

    fn fixed_model<F>(
        &self,
        original: &Model,
        assignment: &[bool],
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> Option<Model>
    where
        F: FnMut() -> bool,
    {
        if assignment.len() != self.master_to_original.len() {
            return None;
        }
        let mut fixed = original.clone();
        for (local, &column) in self.master_to_original.iter().enumerate() {
            if local & 0x3ff == 0 && stopped(deadline, should_stop) {
                return None;
            }
            fixed.fix_col(column, f64::from(u8::from(assignment[local])));
        }
        Some(fixed)
    }
}

fn append_copied_row(
    master: &mut Model,
    original: &Model,
    original_row: usize,
    lb: f64,
    ub: f64,
    terms: &[(Col, f64, BigRational)],
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<()> {
    let mut advice_terms = Vec::with_capacity(terms.len());
    for (index, &(column, advice, _)) in terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        advice_terms.push((column, advice));
    }
    let row = master.add_row(lb, ub, &advice_terms);
    for (index, &(column, advice, ref coefficient)) in terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        if exact(advice).as_ref() != Some(coefficient) {
            master.record_inexact_row_coeff(row, column.0, coefficient.clone());
        }
    }
    if let Some(value) = original.row_lb_exact(original_row, lb) {
        if exact(lb).as_ref() != Some(&value) {
            master.record_inexact_row_bound(row, true, value);
        }
    }
    if let Some(value) = original.row_ub_exact(original_row, ub) {
        if exact(ub).as_ref() != Some(&value) {
            master.record_inexact_row_bound(row, false, value);
        }
    }
    Some(())
}

/// The exact and core views of the PB master.  Both use the same stable local
/// variable indices for the lifetime of the decomposition.
struct MasterState {
    plan: PbRoutePlan,
    instance: PbInstance,
}

#[derive(Clone, Copy)]
struct CutResourceLimits {
    bytes: usize,
    assignment_values: usize,
    pb_terms: usize,
    exact_multipliers: usize,
}

impl CutResourceLimits {
    const fn production() -> Self {
        Self {
            bytes: MAX_RETAINED_CUT_BYTES,
            assignment_values: MAX_RETAINED_ASSIGNMENT_VALUES,
            pb_terms: MAX_RETAINED_PB_TERMS,
            exact_multipliers: MAX_RETAINED_EXACT_MULTIPLIERS,
        }
    }
}

#[derive(Clone, Copy, Default)]
struct CutResourceUsage {
    bytes: usize,
    assignment_values: usize,
    pb_terms: usize,
    exact_multipliers: usize,
}

impl CutResourceUsage {
    fn checked_add(self, other: Self) -> Option<Self> {
        Some(Self {
            bytes: self.bytes.checked_add(other.bytes)?,
            assignment_values: self
                .assignment_values
                .checked_add(other.assignment_values)?,
            pb_terms: self.pb_terms.checked_add(other.pb_terms)?,
            exact_multipliers: self
                .exact_multipliers
                .checked_add(other.exact_multipliers)?,
        })
    }

    fn checked_sub(self, other: Self) -> Option<Self> {
        Some(Self {
            bytes: self.bytes.checked_sub(other.bytes)?,
            assignment_values: self
                .assignment_values
                .checked_sub(other.assignment_values)?,
            pb_terms: self.pb_terms.checked_sub(other.pb_terms)?,
            exact_multipliers: self
                .exact_multipliers
                .checked_sub(other.exact_multipliers)?,
        })
    }

    fn fits(self, limits: CutResourceLimits) -> bool {
        self.bytes <= limits.bytes
            && self.assignment_values <= limits.assignment_values
            && self.pb_terms <= limits.pb_terms
            && self.exact_multipliers <= limits.exact_multipliers
    }
}

struct RetainedCuts {
    licenses: Vec<CutLicense>,
    usage: CutResourceUsage,
    limits: CutResourceLimits,
    first_constraint: usize,
}

impl RetainedCuts {
    fn new(limits: CutResourceLimits, first_constraint: usize) -> Self {
        Self {
            licenses: Vec::new(),
            usage: CutResourceUsage::default(),
            limits,
            first_constraint,
        }
    }

    /// Transactionally retain one already-verified license and its exact PB
    /// restriction.  Every fallible check precedes mutation of either master
    /// representation, so a decline cannot leave a half-installed cut.
    fn retain<F>(
        &mut self,
        master: &mut MasterState,
        license: CutLicense,
        inequality: crate::pb_translate::PbInequality,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> Option<()>
    where
        F: FnMut() -> bool,
    {
        if stopped(deadline, should_stop)
            || master.plan.constraints.len() != master.plan.num_constraints as usize
            || master.instance.constraints.len() != master.instance.num_constraints as usize
            || master.plan.num_constraints != master.instance.num_constraints
            || master.plan.constraints.len()
                != self.first_constraint.checked_add(self.licenses.len())?
        {
            return None;
        }
        let core = core_constraint(&inequality, master.plan.num_vars, deadline, should_stop)?;
        let increment = estimate_retained_cut(&license, &inequality, deadline, should_stop)?;
        let next_usage = self.usage.checked_add(increment)?;
        if !next_usage.fits(self.limits) || stopped(deadline, should_stop) {
            return None;
        }
        let next_constraints = master.plan.num_constraints.checked_add(1)?;

        master.plan.constraints.push(inequality);
        master.plan.num_constraints = next_constraints;
        master.instance.constraints.push(core);
        master.instance.num_constraints = next_constraints;
        self.licenses.push(license);
        self.usage = next_usage;
        Some(())
    }

    /// Tighten every retained generalized-Benders cut to a better incumbent.
    /// All proof reconstruction, resource accounting, and core conversion is
    /// completed before either master representation is mutated.
    fn strengthen_optimality<F>(
        &mut self,
        original: &Model,
        decomposition: &Decomposition,
        master: &mut MasterState,
        incumbent: &BigRational,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> Option<()>
    where
        F: FnMut() -> bool,
    {
        if stopped(deadline, should_stop)
            || master.plan.constraints.len()
                != self.first_constraint.checked_add(self.licenses.len())?
            || master.instance.constraints.len() != master.plan.constraints.len()
        {
            return None;
        }

        let mut replacements = Vec::new();
        let mut next_usage = self.usage;
        for (offset, license) in self.licenses.iter().enumerate() {
            let CutLicense::Optimality {
                assignment,
                row,
                incumbent: old_incumbent,
            } = license
            else {
                continue;
            };
            if stopped(deadline, should_stop) {
                return None;
            }
            if !objective_better(original.sense(), incumbent, old_incumbent) {
                // Equal means there is nothing to do.  A worse target would
                // weaken a proof-bearing master row and is never requested.
                if incumbent == old_incumbent {
                    continue;
                }
                return None;
            }
            let index = self.first_constraint.checked_add(offset)?;
            let old_restriction = master.plan.constraints.get(index)?;
            let old_usage = estimate_retained_cut(license, old_restriction, deadline, should_stop)?;
            let restriction = improvement_inequality(
                original,
                decomposition,
                row,
                incumbent,
                deadline,
                should_stop,
            )?;
            let replacement = CutLicense::Optimality {
                assignment: assignment.clone(),
                row: row.clone(),
                incumbent: incumbent.clone(),
            };
            if !replacement.verify(original, decomposition, deadline, should_stop)
                || !replacement.matches_restriction(
                    original,
                    decomposition,
                    &restriction,
                    deadline,
                    should_stop,
                )
            {
                return None;
            }
            let core = core_constraint(&restriction, master.plan.num_vars, deadline, should_stop)?;
            let replacement_usage =
                estimate_retained_cut(&replacement, &restriction, deadline, should_stop)?;
            next_usage = next_usage
                .checked_sub(old_usage)?
                .checked_add(replacement_usage)?;
            replacements.push((offset, index, restriction, core));
        }

        if !next_usage.fits(self.limits) || stopped(deadline, should_stop) {
            return None;
        }
        for (offset, index, restriction, core) in replacements {
            if let CutLicense::Optimality {
                incumbent: retained,
                ..
            } = &mut self.licenses[offset]
            {
                *retained = incumbent.clone();
            } else {
                // `replacements` was built from this same immutable license
                // vector above; no mutation occurs until this commit loop.
                unreachable!("prepared optimality license changed variant");
            }
            master.plan.constraints[index] = restriction;
            master.instance.constraints[index] = core;
        }
        self.usage = next_usage;
        Some(())
    }

    fn verify_all<F>(
        &self,
        original: &Model,
        decomposition: &Decomposition,
        master: &MasterState,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        if master.plan.constraints.len()
            != self.first_constraint.saturating_add(self.licenses.len())
            || master.instance.constraints.len() != master.plan.constraints.len()
        {
            return false;
        }
        for (offset, license) in self.licenses.iter().enumerate() {
            if stopped(deadline, should_stop)
                || !license.verify(original, decomposition, deadline, should_stop)
            {
                return false;
            }
            let Some(index) = self.first_constraint.checked_add(offset) else {
                return false;
            };
            let Some(restriction) = master.plan.constraints.get(index) else {
                return false;
            };
            if !license.matches_restriction(
                original,
                decomposition,
                restriction,
                deadline,
                should_stop,
            ) {
                return false;
            }
            let Some(core) =
                core_constraint(restriction, master.plan.num_vars, deadline, should_stop)
            else {
                return false;
            };
            if master.instance.constraints.get(index) != Some(&core) {
                return false;
            }
        }
        true
    }
}

/// Replay evidence for one master restriction.
enum CutLicense {
    Certified {
        assignment: Vec<bool>,
        row: CertifiedRow,
    },
    NoGood {
        assignment: Vec<bool>,
        farkas: FarkasCertificate,
    },
    Optimality {
        assignment: Vec<bool>,
        row: CertifiedRow,
        incumbent: BigRational,
    },
}

impl HybridPbLpInfeasibilityCut {
    fn from_license(license: &CutLicense) -> Option<Self> {
        match license {
            CutLicense::Certified { assignment, row } => Some(Self::Certified {
                assignment: assignment.clone(),
                row: HybridCertifiedRow::from_row(row)?,
            }),
            CutLicense::NoGood { assignment, farkas } => Some(Self::NoGood {
                assignment: assignment.clone(),
                farkas: HybridFarkas::from_farkas(farkas)?,
            }),
            // An optimality row can prove exhaustion below an incumbent, but
            // never infeasibility of the original model.
            CutLicense::Optimality { .. } => None,
        }
    }

    fn to_license(&self) -> Option<CutLicense> {
        match self {
            Self::Certified { assignment, row } => Some(CutLicense::Certified {
                assignment: assignment.clone(),
                row: row.to_row()?,
            }),
            Self::NoGood { assignment, farkas } => Some(CutLicense::NoGood {
                assignment: assignment.clone(),
                farkas: farkas.to_farkas()?,
            }),
        }
    }
}

impl HybridCertifiedRow {
    fn from_row(row: &CertifiedRow) -> Option<Self> {
        Some(Self {
            coeffs: row
                .coeffs
                .iter()
                .map(|&(column, ref coefficient)| {
                    (column, HybridRational::from_rational(coefficient))
                })
                .collect(),
            lb: HybridRational::from_rational(&row.lb),
            multipliers: row
                .multipliers
                .iter()
                .map(HybridMultiplier::from_multiplier)
                .collect::<Option<Vec<_>>>()?,
        })
    }

    fn to_row(&self) -> Option<CertifiedRow> {
        Some(CertifiedRow {
            coeffs: self
                .coeffs
                .iter()
                .map(|(column, coefficient)| Some((*column, coefficient.to_rational()?)))
                .collect::<Option<Vec<_>>>()?,
            lb: self.lb.to_rational()?,
            multipliers: self
                .multipliers
                .iter()
                .map(HybridMultiplier::to_multiplier)
                .collect::<Option<Vec<_>>>()?,
        })
    }
}

impl HybridFarkas {
    fn from_farkas(farkas: &FarkasCertificate) -> Option<Self> {
        Some(Self {
            multipliers: farkas
                .multipliers
                .iter()
                .map(HybridMultiplier::from_multiplier)
                .collect::<Option<Vec<_>>>()?,
        })
    }

    fn to_farkas(&self) -> Option<FarkasCertificate> {
        Some(FarkasCertificate {
            multipliers: self
                .multipliers
                .iter()
                .map(HybridMultiplier::to_multiplier)
                .collect::<Option<Vec<_>>>()?,
        })
    }
}

impl HybridMultiplier {
    fn from_multiplier(multiplier: &Multiplier) -> Option<Self> {
        Some(Self {
            fact: HybridFactRef::from_fact(multiplier.fact)?,
            coeff: HybridRational::from_rational(&multiplier.coeff),
        })
    }

    fn to_multiplier(&self) -> Option<Multiplier> {
        Some(Multiplier {
            fact: self.fact.to_fact(),
            coeff: self.coeff.to_rational()?,
        })
    }
}

impl HybridRational {
    fn from_rational(value: &BigRational) -> Self {
        Self {
            numerator: value.numer().clone(),
            denominator: value.denom().clone(),
        }
    }

    fn to_rational(&self) -> Option<BigRational> {
        if self.denominator <= BigInt::zero()
            || self.numerator.gcd(&self.denominator) != BigInt::one()
        {
            return None;
        }
        Some(BigRational::new(
            self.numerator.clone(),
            self.denominator.clone(),
        ))
    }
}

impl HybridFactRef {
    fn from_fact(fact: FactRef) -> Option<Self> {
        match fact {
            FactRef::RowBound {
                row,
                side: BoundSide::Lower,
            } => Some(Self::RowLower { row: row.0 }),
            FactRef::RowBound {
                row,
                side: BoundSide::Upper,
            } => Some(Self::RowUpper { row: row.0 }),
            FactRef::ColBound {
                col,
                side: BoundSide::Lower,
            } => Some(Self::ColLower { col: col.0 }),
            FactRef::ColBound {
                col,
                side: BoundSide::Upper,
            } => Some(Self::ColUpper { col: col.0 }),
            #[allow(unreachable_patterns)]
            _ => None,
        }
    }

    fn to_fact(self) -> FactRef {
        match self {
            Self::RowLower { row } => FactRef::RowBound {
                row: Row(row),
                side: BoundSide::Lower,
            },
            Self::RowUpper { row } => FactRef::RowBound {
                row: Row(row),
                side: BoundSide::Upper,
            },
            Self::ColLower { col } => FactRef::ColBound {
                col: Col(col),
                side: BoundSide::Lower,
            },
            Self::ColUpper { col } => FactRef::ColBound {
                col: Col(col),
                side: BoundSide::Upper,
            },
        }
    }
}

impl CutLicense {
    fn verify<F>(
        &self,
        original: &Model,
        decomposition: &Decomposition,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        if stopped(deadline, should_stop) {
            return false;
        }
        match self {
            Self::Certified { assignment, row } => {
                if row.verify(original).is_err() || stopped(deadline, should_stop) {
                    return false;
                }
                for (index, &(column, _)) in row.coeffs.iter().enumerate() {
                    if index & 0x3ff == 0 && stopped(deadline, should_stop) {
                        return false;
                    }
                    if !is_master_column(decomposition, column as usize) {
                        return false;
                    }
                }
                cut_violated(row, decomposition, assignment, deadline, should_stop)
            }
            Self::NoGood { assignment, farkas } => decomposition
                .fixed_model(original, assignment, deadline, should_stop)
                .is_some_and(|fixed| {
                    farkas.verify(&fixed).is_ok() && !stopped(deadline, should_stop)
                }),
            Self::Optimality {
                assignment,
                row,
                incumbent,
            } => {
                if assignment.len() != decomposition.master_to_original.len()
                    || row.verify(original).is_err()
                    || !projected_optimality_row_valid(
                        original,
                        decomposition,
                        row,
                        deadline,
                        should_stop,
                    )
                {
                    return false;
                }
                improvement_inequality(
                    original,
                    decomposition,
                    row,
                    incumbent,
                    deadline,
                    should_stop,
                )
                .and_then(|restriction| {
                    pb_inequality_satisfied(&restriction, assignment, deadline, should_stop)
                })
                .is_some_and(|satisfied| !satisfied)
            }
        }
    }

    /// Independently reconstruct the PB restriction licensed by this proof.
    /// This guards the direct append boundary as well as final exhaustion: a
    /// valid Farkas object cannot license an unrelated or accidentally
    /// mis-indexed master row.
    fn matches_restriction<F>(
        &self,
        original: &Model,
        decomposition: &Decomposition,
        restriction: &crate::pb_translate::PbInequality,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        let rebuilt = match self {
            Self::Certified { row, .. } => {
                certified_cut_inequality(decomposition, row, deadline, should_stop)
            }
            Self::NoGood { assignment, .. } => no_good_inequality(
                decomposition.master_to_original.len() as u32,
                assignment,
                deadline,
                should_stop,
            ),
            Self::Optimality { row, incumbent, .. } => improvement_inequality(
                original,
                decomposition,
                row,
                incumbent,
                deadline,
                should_stop,
            ),
        };
        rebuilt.as_ref() == Some(restriction)
    }
}

/// Remove temporary master-bound facts from a leaf Farkas proof.  The
/// remaining positive combination is a globally valid row in the original
/// model and, because master bounds were the only removed facts, must contain
/// no continuous coefficient.
fn project_farkas_row(
    original: &Model,
    decomposition: &Decomposition,
    assignment: &[bool],
    farkas: &FarkasCertificate,
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<CertifiedRow> {
    let mut multipliers = Vec::with_capacity(farkas.multipliers.len());
    for (index, multiplier) in farkas.multipliers.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let keep = match multiplier.fact {
            FactRef::ColBound { col, .. } => !is_master_column(decomposition, col.index()),
            FactRef::RowBound { .. } => true,
        };
        if keep {
            multipliers.push(multiplier.clone());
        }
    }
    let row = CertifiedRow::from_multipliers(original, multipliers).ok()?;
    if stopped(deadline, should_stop) {
        return None;
    }
    for (index, &(column, _)) in row.coeffs.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        if !is_master_column(decomposition, column as usize) {
            return None;
        }
    }
    if !cut_violated(&row, decomposition, assignment, deadline, should_stop) {
        return None;
    }
    Some(row)
}

fn is_master_column(decomposition: &Decomposition, original: usize) -> bool {
    matches!(
        decomposition.original_to_master.get(original),
        Some(Some(_))
    )
}

fn cut_violated(
    row: &CertifiedRow,
    decomposition: &Decomposition,
    assignment: &[bool],
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> bool {
    if assignment.len() != decomposition.master_to_original.len() {
        return false;
    }
    let mut lhs = BigRational::zero();
    for (index, &(original, ref coefficient)) in row.coeffs.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return false;
        }
        let Some(Some(local)) = decomposition
            .original_to_master
            .get(original as usize)
            .copied()
        else {
            return false;
        };
        if assignment[local.index()] {
            lhs += coefficient;
        }
    }
    lhs < row.lb
}

fn objective_better(sense: Sense, candidate: &BigRational, incumbent: &BigRational) -> bool {
    match sense {
        Sense::Minimize => candidate < incumbent,
        Sense::Maximize => candidate > incumbent,
    }
}

fn oriented(sense: Sense, value: &BigRational) -> BigRational {
    match sense {
        Sense::Minimize => value.clone(),
        Sense::Maximize => -value.clone(),
    }
}

fn continuous_objective_terms<F>(
    model: &Model,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<Vec<(u32, BigRational)>>
where
    F: FnMut() -> bool,
{
    let mut objective = Vec::new();
    for j in 0..model.num_cols() {
        if j & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let column = Col(j as u32);
        if !matches!(model.col_kind(column), ColKind::Continuous) {
            continue;
        }
        let advice = model.obj_coeff(column);
        let coefficient = model.obj_coeff_exact_at(j as u32, advice);
        if !coefficient.is_zero() {
            objective.push((j as u32, coefficient));
        }
    }
    Some(objective)
}

fn continuous_objective_value<F>(
    model: &Model,
    values: &[BigRational],
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<BigRational>
where
    F: FnMut() -> bool,
{
    if values.len() != model.num_cols() {
        return None;
    }
    let mut value = BigRational::zero();
    for (j, coefficient) in continuous_objective_terms(model, deadline, should_stop)? {
        value += coefficient * &values[j as usize];
    }
    Some(value)
}

/// Remove fixed-master bound facts from an exact fixed-LP optimum.  The
/// resulting combination is accepted only if it independently proves, against
/// the original model, a row whose continuous coefficients are exactly the
/// oriented continuous objective.  A certificate valid merely under the
/// assignment box therefore cannot escape this boundary.
fn project_optimality_row<F>(
    original: &Model,
    decomposition: &Decomposition,
    assignment: &[bool],
    values: &[BigRational],
    certificate: &OptimalityCertificate,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<CertifiedRow>
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) || certificate.sense != original.sense() {
        return None;
    }
    let expected_objective = continuous_objective_terms(original, deadline, should_stop)?;
    if certificate.objective.as_slice() != expected_objective.as_slice() {
        return None;
    }
    let achieved = continuous_objective_value(original, values, deadline, should_stop)?;
    if &achieved != &certificate.bound {
        return None;
    }
    let fixed = decomposition.fixed_model(original, assignment, deadline, should_stop)?;
    certificate.verify(&fixed).ok()?;
    if fixed.check_point(values).is_err() || original.check_point(values).is_err() {
        return None;
    }

    let mut multipliers = Vec::with_capacity(certificate.multipliers.len());
    for (index, multiplier) in certificate.multipliers.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let assignment_fact = matches!(
            multiplier.fact,
            FactRef::ColBound { col, .. }
                if is_master_column(decomposition, col.index())
        );
        if !assignment_fact {
            multipliers.push(multiplier.clone());
        }
    }
    let row = CertifiedRow::from_multipliers(original, multipliers).ok()?;
    if !projected_optimality_row_valid(original, decomposition, &row, deadline, should_stop) {
        return None;
    }
    let mut lhs = BigRational::zero();
    for (index, &(column, ref coefficient)) in row.coeffs.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        lhs += coefficient * values.get(column as usize)?;
    }
    (lhs == row.lb).then_some(row)
}

fn projected_optimality_row_valid<F>(
    original: &Model,
    decomposition: &Decomposition,
    row: &CertifiedRow,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> bool
where
    F: FnMut() -> bool,
{
    if !decomposition.has_continuous_objective || row.verify(original).is_err() {
        return false;
    }
    let mut actual = vec![BigRational::zero(); original.num_cols()];
    for (index, &(column, ref coefficient)) in row.coeffs.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return false;
        }
        let Some(slot) = actual.get_mut(column as usize) else {
            return false;
        };
        *slot += coefficient;
    }
    for (j, coefficient) in actual.iter().enumerate() {
        if j & 0x3ff == 0 && stopped(deadline, should_stop) {
            return false;
        }
        if is_master_column(decomposition, j) {
            continue;
        }
        let column = Col(j as u32);
        if !matches!(original.col_kind(column), ColKind::Continuous) {
            return false;
        }
        let advice = original.obj_coeff(column);
        let expected = oriented(
            original.sense(),
            &original.obj_coeff_exact_at(j as u32, advice),
        );
        if coefficient != &expected {
            return false;
        }
    }
    true
}

/// Convert the strict generalized-Benders condition
///
/// `oriented(total objective lower bound at x) < oriented(incumbent)`
///
/// into one exact integer PB `>=` row.  Clearing every denominator makes both
/// sides integral; strict `<` is therefore exactly one integer unit stronger
/// than `<=`.
fn improvement_inequality<F>(
    original: &Model,
    decomposition: &Decomposition,
    row: &CertifiedRow,
    incumbent: &BigRational,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<crate::pb_translate::PbInequality>
where
    F: FnMut() -> bool,
{
    if !projected_optimality_row_valid(original, decomposition, row, deadline, should_stop) {
        return None;
    }
    let mut coefficients = Vec::with_capacity(decomposition.master_to_original.len());
    for (local, &column) in decomposition.master_to_original.iter().enumerate() {
        if local & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let advice = original.obj_coeff(column);
        coefficients.push(oriented(
            original.sense(),
            &original.obj_coeff_exact_at(column.0, advice),
        ));
    }
    for (index, &(column, ref coefficient)) in row.coeffs.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        if let Some(Some(local)) = decomposition
            .original_to_master
            .get(column as usize)
            .copied()
        {
            coefficients[local.index()] -= coefficient;
        }
    }

    let constant = &row.lb + oriented(original.sense(), &original.obj_offset_exact());
    let target = oriented(original.sense(), incumbent);
    let delta = constant - target;
    let mut denominator = delta.denom().clone();
    for (index, coefficient) in coefficients.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        denominator = denominator.lcm(coefficient.denom());
    }
    let scale = |value: &BigRational| -> Option<i128> {
        (value.numer() * (&denominator / value.denom())).to_i128()
    };

    let mut terms = Vec::new();
    for (column, coefficient) in coefficients.iter().enumerate() {
        if column & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let coefficient = scale(coefficient)?.checked_neg()?;
        if coefficient != 0 {
            terms.push((column as u32, coefficient));
        }
    }
    let rhs = scale(&delta)?.checked_add(1)?;
    let mut inequality = crate::pb_translate::PbInequality { terms, rhs };
    let mut gcd = 0i128;
    for (index, &(_, coefficient)) in inequality.terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        gcd = gcd.gcd(&coefficient.checked_abs()?);
    }
    if gcd > 1 {
        for (_, coefficient) in &mut inequality.terms {
            *coefficient /= gcd;
        }
        inequality.rhs = BigInt::from(inequality.rhs)
            .div_ceil(&BigInt::from(gcd))
            .to_i128()?;
    }
    pb_core_row_range_fits(&inequality, deadline, should_stop).then_some(inequality)
}

fn pb_inequality_satisfied<F>(
    row: &crate::pb_translate::PbInequality,
    assignment: &[bool],
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<bool>
where
    F: FnMut() -> bool,
{
    let mut lhs = 0i128;
    for (index, &(column, coefficient)) in row.terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let value = *assignment.get(column as usize)?;
        if value {
            lhs = lhs.checked_add(coefficient)?;
        }
    }
    Some(lhs >= row.rhs)
}

/// Convert a proved exact row directly into its PB-master representation.
/// This is the same exact Boolean-grid normalization used by `pb_translate`:
/// clear coefficient denominators, ceil the scaled rhs, then divide by the
/// coefficient GCD.  No floating advice participates.
fn certified_cut_inequality(
    decomposition: &Decomposition,
    cut: &CertifiedRow,
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<crate::pb_translate::PbInequality> {
    let mut exact_terms = Vec::with_capacity(cut.coeffs.len());
    let mut denominator = BigInt::one();
    for (index, &(original, ref coefficient)) in cut.coeffs.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let Some(Some(local)) = decomposition
            .original_to_master
            .get(original as usize)
            .copied()
        else {
            return None;
        };
        if !coefficient.is_zero() {
            denominator = denominator.lcm(coefficient.denom());
            exact_terms.push((local.0, coefficient));
        }
    }
    let mut terms = Vec::with_capacity(exact_terms.len());
    for (index, &(column, coefficient)) in exact_terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let multiplier = &denominator / coefficient.denom();
        let value = (coefficient.numer() * multiplier)
            .to_i128()
            .filter(|&value| value != i128::MIN)?;
        terms.push((column, value));
    }
    let rhs = (cut.lb.numer() * &denominator)
        .div_ceil(cut.lb.denom())
        .to_i128()?;
    let mut inequality = crate::pb_translate::PbInequality { terms, rhs };
    let mut gcd = 0i128;
    for (index, &(_, coefficient)) in inequality.terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        gcd = gcd.gcd(&coefficient.abs());
    }
    if gcd > 1 {
        for (_, coefficient) in &mut inequality.terms {
            *coefficient /= gcd;
        }
        inequality.rhs = BigInt::from(inequality.rhs)
            .div_ceil(&BigInt::from(gcd))
            .to_i128()?;
    }
    pb_core_row_range_fits(&inequality, deadline, should_stop).then_some(inequality)
}

fn no_good_inequality(
    num_vars: u32,
    assignment: &[bool],
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<crate::pb_translate::PbInequality> {
    if assignment.len() != num_vars as usize {
        return None;
    }
    let mut terms = Vec::with_capacity(assignment.len());
    let mut ones = 0i128;
    for (j, &value) in assignment.iter().enumerate() {
        if j & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        if value {
            ones = ones.checked_add(1)?;
            terms.push((j as u32, -1));
        } else {
            terms.push((j as u32, 1));
        }
    }
    let rhs = 1i128.checked_sub(ones)?;
    Some(crate::pb_translate::PbInequality { terms, rhs })
}

fn pb_core_row_range_fits(
    row: &crate::pb_translate::PbInequality,
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> bool {
    let mut normalized_rhs = row.rhs;
    let mut total_weight = 0i128;
    for (index, &(_, coefficient)) in row.terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return false;
        }
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

fn estimate_retained_cut(
    license: &CutLicense,
    inequality: &crate::pb_translate::PbInequality,
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<CutResourceUsage> {
    let (assignment, multipliers, certified_row, incumbent) = match license {
        CutLicense::Certified { assignment, row } => {
            (assignment, row.multipliers.as_slice(), Some(row), None)
        }
        CutLicense::NoGood { assignment, farkas } => {
            (assignment, farkas.multipliers.as_slice(), None, None)
        }
        CutLicense::Optimality {
            assignment,
            row,
            incumbent,
        } => (
            assignment,
            row.multipliers.as_slice(),
            Some(row),
            Some(incumbent),
        ),
    };
    let mut bytes = size_of::<CutLicense>()
        .checked_add(assignment.len().checked_mul(size_of::<bool>())?)?
        .checked_add(size_of::<crate::pb_translate::PbInequality>())?
        .checked_add(
            inequality
                .terms
                .len()
                .checked_mul(size_of::<(u32, i128)>())?,
        )?
        .checked_add(size_of::<PbConstraint>())?
        .checked_add(
            inequality
                .terms
                .len()
                .checked_mul(size_of::<PbTerm>().checked_add(size_of::<PbLit>())?)?,
        )?;
    if let Some(incumbent) = incumbent {
        bytes = bytes
            .checked_add(size_of::<BigRational>())?
            .checked_add(rational_payload_bytes(incumbent)?)?;
    }

    let mut exact_terms = 0usize;
    if let Some(row) = certified_row {
        bytes = bytes
            .checked_add(size_of::<CertifiedRow>())?
            .checked_add(size_of::<BigRational>())?
            .checked_add(rational_payload_bytes(&row.lb)?)?;
        for (index, (_, coefficient)) in row.coeffs.iter().enumerate() {
            if index & 0x3ff == 0 && stopped(deadline, should_stop) {
                return None;
            }
            bytes = bytes
                .checked_add(size_of::<(u32, BigRational)>())?
                .checked_add(rational_payload_bytes(coefficient)?)?;
            exact_terms = exact_terms.checked_add(1)?;
        }
    }
    for (index, multiplier) in multipliers.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        bytes = bytes
            .checked_add(size_of::<Multiplier>())?
            .checked_add(rational_payload_bytes(&multiplier.coeff)?)?;
    }

    Some(CutResourceUsage {
        bytes,
        assignment_values: assignment.len(),
        // The exact plan and core instance retain separate term vectors; an
        // exact certified row is a third retained term vector in its license.
        pb_terms: inequality
            .terms
            .len()
            .checked_mul(2)?
            .checked_add(exact_terms)?,
        exact_multipliers: multipliers.len(),
    })
}

fn rational_payload_bytes(value: &BigRational) -> Option<usize> {
    bigint_payload_bytes(value.numer())?.checked_add(bigint_payload_bytes(value.denom())?)
}

fn bigint_payload_bytes(value: &BigInt) -> Option<usize> {
    let bytes = usize::try_from(value.bits().checked_add(7)? / 8).ok()?;
    let word = size_of::<usize>();
    bytes
        .checked_add(word.checked_sub(1)?)?
        .checked_div(word)?
        .checked_mul(word)
}

struct ContinuousSubproblem {
    lp: FloatLp,
    warm: Option<(Vec<usize>, Vec<NbBound>)>,
    has_objective: bool,
}

enum SubproblemDecision {
    Feasible(Vec<BigRational>),
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
        dual_row: CertifiedRow,
    },
    Infeasible(FarkasCertificate),
}

impl ContinuousSubproblem {
    fn new<F>(model: &Model, deadline: Option<Instant>, should_stop: &mut F) -> Option<Self>
    where
        F: FnMut() -> bool,
    {
        let objective: Vec<(u32, f64)> = continuous_objective_terms(model, deadline, should_stop)?
            .into_iter()
            .map(|(column, _)| (column, model.obj_coeff(Col(column))))
            .collect();
        let has_objective = !objective.is_empty();
        let lp = FloatLp::from_model(
            model,
            &objective,
            if has_objective {
                model.sense()
            } else {
                Sense::Minimize
            },
        )?;
        if stopped(deadline, should_stop) {
            return None;
        }
        Some(Self {
            lp,
            warm: None,
            has_objective,
        })
    }

    fn check<F>(
        &mut self,
        original: &Model,
        decomposition: &Decomposition,
        assignment: &[bool],
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> Option<SubproblemDecision>
    where
        F: FnMut() -> bool,
    {
        if stopped(deadline, should_stop) {
            return None;
        }
        let fixed = decomposition.fixed_model(original, assignment, deadline, should_stop)?;
        let mut lower = self.lp.lower.clone();
        let mut upper = self.lp.upper.clone();
        for (local, &original_column) in decomposition.master_to_original.iter().enumerate() {
            if local & 0x3ff == 0 && stopped(deadline, should_stop) {
                return None;
            }
            let value = f64::from(u8::from(assignment[local]));
            lower[original_column.index()] = value;
            upper[original_column.index()] = value;
        }
        let warm = self
            .warm
            .as_ref()
            .map(|(basis, at)| (basis.as_slice(), at.as_slice()));
        let candidate = self.lp.solve_bounded(&lower, &upper, warm, deadline);
        self.warm = Some((candidate.basis.clone(), candidate.at.clone()));
        if stopped(deadline, should_stop) {
            return None;
        }

        match candidate.status {
            SimplexStatus::PrimalInfeasible => {
                if let Some(farkas) = exact_farkas_from_float_ray(&fixed, &candidate.farkas) {
                    return Some(SubproblemDecision::Infeasible(farkas));
                }
                if self.has_objective {
                    exact_optimized_subproblem(
                        &fixed,
                        original,
                        decomposition,
                        assignment,
                        deadline,
                        should_stop,
                    )
                } else {
                    exact_subproblem(&fixed, original, deadline, should_stop)
                }
            }
            SimplexStatus::Optimal => {
                if self.has_objective {
                    if let Some(certified) =
                        certify_bounded_by(&fixed, &self.lp, &candidate, &lower, &upper, deadline)
                    {
                        if !stopped(deadline, should_stop)
                            && continuous_objective_value(
                                original,
                                &certified.values,
                                deadline,
                                should_stop,
                            )
                            .as_ref()
                                == Some(&certified.value)
                        {
                            if let Some(dual_row) = project_optimality_row(
                                original,
                                decomposition,
                                assignment,
                                &certified.values,
                                &certified.cert,
                                deadline,
                                should_stop,
                            ) {
                                let value = original.objective_value_at(&certified.values);
                                return Some(SubproblemDecision::Optimal {
                                    value,
                                    model_values: certified.values,
                                    dual_row,
                                });
                            }
                        }
                    }
                    return exact_optimized_subproblem(
                        &fixed,
                        original,
                        decomposition,
                        assignment,
                        deadline,
                        should_stop,
                    );
                }
                if let Some(point) =
                    cheap_exact_point(&fixed, original, &candidate, deadline, should_stop)
                {
                    return Some(SubproblemDecision::Feasible(point));
                }
                if let Some(certified) =
                    certify_bounded_by(&fixed, &self.lp, &candidate, &lower, &upper, deadline)
                {
                    if fixed.check_point(&certified.values).is_ok()
                        && original.check_point(&certified.values).is_ok()
                    {
                        return Some(SubproblemDecision::Feasible(certified.values));
                    }
                }
                exact_subproblem(&fixed, original, deadline, should_stop)
            }
            SimplexStatus::Unbounded if self.has_objective => exact_optimized_subproblem(
                &fixed,
                original,
                decomposition,
                assignment,
                deadline,
                should_stop,
            ),
            SimplexStatus::OutOfMemory
            | SimplexStatus::Stopped
            | SimplexStatus::Unbounded
            | SimplexStatus::Cutoff => None,
        }
    }
}

fn exact_optimized_subproblem<F>(
    fixed: &Model,
    original: &Model,
    decomposition: &Decomposition,
    assignment: &[bool],
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<SubproblemDecision>
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) {
        return None;
    }
    let budget = Budget {
        deadline,
        max_iters: Budget::default_iters(fixed.num_cols() + fixed.num_rows()),
    };
    let mut lp = ExactLp::new_within(fixed, deadline)?;
    let user_objective = continuous_objective_terms(original, deadline, should_stop)?;
    let minimize_objective: Vec<(u32, Rational)> = user_objective
        .iter()
        .map(|&(column, ref coefficient)| {
            (
                column,
                Rational::from_big(oriented(original.sense(), coefficient)),
            )
        })
        .collect();
    let result = lp.minimize(&minimize_objective, &budget);
    if stopped(deadline, should_stop) {
        return None;
    }
    match result {
        LpOptimum::Optimal { value, multipliers } => {
            let user_value = oriented(original.sense(), &value);
            let certificate = OptimalityCertificate {
                sense: original.sense(),
                objective: user_objective,
                bound: user_value.clone(),
                multipliers,
            };
            certificate.verify(fixed).ok()?;
            let model_values = lp.structural_values();
            if fixed.check_point(&model_values).is_err()
                || original.check_point(&model_values).is_err()
                || continuous_objective_value(original, &model_values, deadline, should_stop)?
                    != user_value
            {
                return None;
            }
            let dual_row = project_optimality_row(
                original,
                decomposition,
                assignment,
                &model_values,
                &certificate,
                deadline,
                should_stop,
            )?;
            let value = original.objective_value_at(&model_values);
            Some(SubproblemDecision::Optimal {
                value,
                model_values,
                dual_row,
            })
        }
        LpOptimum::Infeasible(farkas) => {
            farkas.verify(fixed).ok()?;
            Some(SubproblemDecision::Infeasible(farkas))
        }
        LpOptimum::Unbounded | LpOptimum::Unknown(_) => None,
    }
}

fn cheap_exact_point(
    fixed: &Model,
    original: &Model,
    candidate: &Candidate,
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<Vec<BigRational>> {
    let n = original.num_cols();
    if candidate.values.len() < n {
        return None;
    }
    for (index, value) in candidate.values[..n].iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        if !value.is_finite() {
            return None;
        }
    }

    // Network and assignment LPs commonly have integral vertices.  Rounding is
    // advice only; the two exact checks below are the authority.
    let mut rounded = Vec::with_capacity(n);
    let mut all_roundable = true;
    for (index, value) in candidate.values[..n].iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        let value = value.round();
        if value.abs() > (1u64 << 52) as f64 {
            all_roundable = false;
            break;
        }
        rounded.push(BigRational::from_integer(BigInt::from(value as i64)));
    }
    if all_roundable {
        let point = rounded;
        if fixed.check_point(&point).is_ok() && original.check_point(&point).is_ok() {
            return Some(point);
        }
    }

    // A genuinely dyadic float vertex can occasionally check exactly too.
    let mut point = Vec::with_capacity(n);
    for (index, &value) in candidate.values[..n].iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        point.push(exact(value)?);
    }
    (fixed.check_point(&point).is_ok() && original.check_point(&point).is_ok()).then_some(point)
}

fn exact_subproblem<F>(
    fixed: &Model,
    original: &Model,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<SubproblemDecision>
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) {
        return None;
    }
    let budget = Budget {
        deadline,
        max_iters: Budget::default_iters(fixed.num_cols() + fixed.num_rows()),
    };
    let mut lp = ExactLp::new_within(fixed, deadline)?;
    let result = lp.make_feasible(&budget);
    // ExactLp receives the wall deadline through `Budget`.  Its API has no
    // callback hook, so the arbitrary non-Send caller predicate is checked at
    // both synchronous boundaries and any completed result is discarded after
    // cancellation.
    if stopped(deadline, should_stop) {
        return None;
    }
    match result {
        LpFeasibility::Feasible => {
            let point = lp.structural_values();
            (fixed.check_point(&point).is_ok() && original.check_point(&point).is_ok())
                .then_some(SubproblemDecision::Feasible(point))
        }
        LpFeasibility::Infeasible(farkas) => {
            farkas.verify(fixed).ok()?;
            Some(SubproblemDecision::Infeasible(farkas))
        }
        LpFeasibility::Unknown(_) => None,
    }
}

/// Local adapter: the decomposition is intentionally not coupled to raw CDCL.
/// Today it uses AY's sequential PB portfolio; the adapter boundary lets
/// measurement swap in a persistent/incremental master without touching any LP
/// or proof logic.
enum MasterSolve {
    Candidate {
        assignment: Vec<bool>,
        claimed_objective: Option<i128>,
        proven_optimal: bool,
    },
    Infeasible,
}

fn solve_master<F>(
    instance: &PbInstance,
    objective: Option<&PbObjective>,
    plan: &PbRoutePlan,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<MasterSolve>
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) {
        return None;
    }
    let start = Instant::now();
    let timeout = deadline.map(|limit| limit.saturating_duration_since(start));
    if timeout.is_some_and(|duration| duration.is_zero()) {
        return None;
    }
    // The portfolio receives the route's remaining wall budget directly.  Its
    // synchronous API accepts an `AtomicBool`, whereas this entry point accepts
    // an arbitrary `FnMut` that need not be Send or thread-safe; it would be
    // unsound to pretend that predicate can be polled from a watchdog thread.
    // We therefore check it immediately before and after the call.  Deadline
    // cancellation is enforced inside the portfolio by `timeout`.
    let term = AtomicBool::new(false);
    let solution = match objective {
        Some(objective) => {
            let mut ignore_improvement = |_: i128, _: &[bool]| {};
            solve_optimization_portfolio(
                instance,
                objective,
                timeout,
                start,
                &term,
                &mut ignore_improvement,
            )
        }
        None => solve_decision_portfolio(instance, timeout, start, &term),
    };
    if stopped(deadline, should_stop) {
        return None;
    }

    match solution.status {
        PbStatus::Unsatisfiable => Some(MasterSolve::Infeasible),
        PbStatus::Satisfiable | PbStatus::OptimumFound => {
            if solution.assignment.len() < plan.num_vars as usize
                || !verify_all_constraints(&instance.constraints, &solution.assignment)
                || !plan.satisfies(&solution.assignment)
            {
                return None;
            }
            let claimed_objective = match plan.objective.as_ref() {
                Some(objective_plan) => {
                    let claimed = solution.objective?;
                    if objective_plan.value_at(&solution.assignment)? != claimed {
                        return None;
                    }
                    Some(claimed)
                }
                None => {
                    if solution.status == PbStatus::OptimumFound {
                        return None;
                    }
                    None
                }
            };
            Some(MasterSolve::Candidate {
                assignment: solution.assignment[..plan.num_vars as usize].to_vec(),
                claimed_objective,
                proven_optimal: solution.status == PbStatus::OptimumFound,
            })
        }
        PbStatus::Unknown | PbStatus::Unsupported => None,
    }
}

fn core_instance<F>(
    plan: &PbRoutePlan,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Option<PbInstance>
where
    F: FnMut() -> bool,
{
    let mut constraints = Vec::with_capacity(plan.constraints.len());
    for (index, row) in plan.constraints.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        constraints.push(core_constraint(row, plan.num_vars, deadline, should_stop)?);
    }
    if constraints.len() != plan.num_constraints as usize {
        return None;
    }
    let objective = match plan.objective.as_ref() {
        Some(objective) => Some(core_objective(
            objective,
            plan.num_vars,
            deadline,
            should_stop,
        )?),
        None => None,
    };
    Some(PbInstance {
        num_vars: plan.num_vars,
        num_constraints: plan.num_constraints,
        constraints,
        objective,
    })
}

fn core_constraint(
    row: &crate::pb_translate::PbInequality,
    num_vars: u32,
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<PbConstraint> {
    let mut terms = Vec::with_capacity(row.terms.len());
    for (index, &(column, coeff)) in row.terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        if column >= num_vars {
            return None;
        }
        terms.push(PbTerm {
            coeff,
            lits: vec![PbLit {
                var: column.checked_add(1)?,
                negated: false,
            }],
        });
    }
    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: row.rhs,
    })
}

fn core_objective(
    objective: &PbObjectivePlan,
    num_vars: u32,
    deadline: Option<Instant>,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<PbObjective> {
    let mut terms = Vec::with_capacity(objective.terms.len());
    for (index, &(column, coeff)) in objective.terms.iter().enumerate() {
        if index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return None;
        }
        if column >= num_vars {
            return None;
        }
        terms.push(PbTerm {
            coeff,
            lits: vec![PbLit {
                var: column.checked_add(1)?,
                negated: false,
            }],
        });
    }
    Some(PbObjective { terms })
}

fn stopped<F>(deadline: Option<Instant>, should_stop: &mut F) -> bool
where
    F: FnMut() -> bool,
{
    deadline_reached(deadline) || should_stop()
}

fn deadline_reached(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|limit| Instant::now() >= limit)
}

/// Cached trace predicate. `tests/env_ledger.rs` counts a bare `env::var_os` on
/// the solve path as a LIVE read — a fresh `getenv` a concurrent `set_var` can
/// race — and that ratchet may only move DOWN.
fn trace_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}

fn trace_result(decomposition: &Decomposition, cuts: usize, verdict: &str, elapsed: Duration) {
    if trace_enabled() {
        eprintln!(
            "--trace hybrid-pb-lp: master={} coupling_rows={} cuts={} \
             verdict={} wall={:.6}s",
            decomposition.master_to_original.len(),
            decomposition.coupling_rows,
            cuts,
            verdict,
            elapsed.as_secs_f64(),
        );
    }
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}

#[cfg(test)]
mod tests {
    use super::*;

    fn integer(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    fn rational(numerator: BigInt, denominator: BigInt) -> BigRational {
        BigRational::new(numerator, denominator)
    }

    fn admit(model: &Model) -> Decomposition {
        Decomposition::admit(model, None, &mut || false).expect("admitted")
    }

    fn master_state(decomposition: &Decomposition) -> MasterState {
        let plan = translate(&decomposition.master, None).expect("PB plan");
        let instance = core_instance(&plan, None, &mut || false).expect("core instance");
        MasterState { plan, instance }
    }

    fn fixed_charge_model(required: f64) -> Model {
        let mut model = Model::new();
        let open = model.add_binary_col();
        let flow = model.add_col(0.0, f64::INFINITY);
        // flow <= open
        model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (open, -1.0)]);
        // flow >= required
        model.add_row(required, f64::INFINITY, &[(flow, 1.0)]);
        model.set_objective(&[(open, 1.0)], Sense::Minimize);
        model
    }

    #[test]
    fn projected_farkas_cut_is_global_and_excludes_assignment() {
        let model = fixed_charge_model(1.0);
        let decomposition = admit(&model);
        let mut checker = ContinuousSubproblem::new(&model, None, &mut || false).expect("LP");
        let SubproblemDecision::Infeasible(farkas) = checker
            .check(&model, &decomposition, &[false], None, &mut || false)
            .expect("subproblem result")
        else {
            panic!("closed arc must be infeasible");
        };
        let row = project_farkas_row(&model, &decomposition, &[false], &farkas, None, &mut || {
            false
        })
        .expect("Benders row");
        row.verify(&model).expect("global exact proof");
        assert!(cut_violated(
            &row,
            &decomposition,
            &[false],
            None,
            &mut || false
        ));
        assert!(!cut_violated(
            &row,
            &decomposition,
            &[true],
            None,
            &mut || false
        ));
    }

    #[test]
    fn hybrid_route_proves_fixed_charge_optimum() {
        let model = fixed_charge_model(1.0);
        let decision = try_solve(&model, None).expect("hybrid result");
        let HybridPbLpDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected optimum");
        };
        assert_eq!(value, integer(1));
        assert_eq!(model_values[0], integer(1));
        model.check_point(&model_values).expect("exact witness");
    }

    #[test]
    fn hybrid_route_proves_master_exhaustion_infeasible() {
        let model = fixed_charge_model(2.0);
        let decision = try_solve(&model, None).expect("hybrid result");
        assert!(matches!(decision, HybridPbLpDecision::Infeasible));
    }

    #[test]
    fn certified_hybrid_infeasibility_round_trips_and_replays() {
        let model = fixed_charge_model(2.0);
        let CertifiedHybridPbLpDecision::Infeasible(certificate) =
            try_solve_certified(&model, None).expect("certified hybrid result")
        else {
            panic!("expected certified infeasibility");
        };
        assert!(!certificate.cuts.is_empty());
        verify_hybrid_pb_lp_infeasibility_certificate(&model, &certificate)
            .expect("generated artifact independently replays");

        let encoded = encode_hybrid_pb_lp_infeasibility_certificate_json(&certificate)
            .expect("bounded JSON encoding");
        let decoded = decode_hybrid_pb_lp_infeasibility_certificate_json(&encoded)
            .expect("bounded JSON decoding");
        assert_eq!(decoded, certificate);
        verify_hybrid_pb_lp_infeasibility_certificate(&model, &decoded)
            .expect("decoded artifact independently replays");
    }

    /// TWO master binaries and a projected Benders row that separates only SOME
    /// of their assignments.
    ///
    /// `flow <= 2a + 2b` with `flow >= 3` gives the Farkas row `2a + 2b >= 3`,
    /// which excludes (0,0), (1,0) and (0,1) but NOT (1,1); the pure-master row
    /// `a + b <= 1` is what closes the search. That gap is the point: it makes
    /// the recorded `assignment` load-bearing, so a cut credited to an
    /// assignment it does not cut off can actually be detected.
    ///
    /// The single-binary `fixed_charge_model(2.0)` cannot do this. Its cut is
    /// the globally infeasible `open >= 2`, whose lhs is 0 at open=false and 1
    /// at open=true — both below 2, so both count as "violated" and flipping the
    /// bit is INERT. That is why this test passed for years while `cut_violated`
    /// went untested.
    fn separating_cut_model() -> Model {
        let mut model = Model::new();
        let a = model.add_binary_col();
        let b = model.add_binary_col();
        let flow = model.add_col(0.0, f64::INFINITY);
        // flow <= 2a + 2b
        model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (a, -2.0), (b, -2.0)]);
        // flow >= 3
        model.add_row(3.0, f64::INFINITY, &[(flow, 1.0)]);
        // at most one may open — a pure master row
        model.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);
        model.set_objective(&[(a, 1.0), (b, 1.0)], Sense::Minimize);
        model
    }

    #[test]
    fn certified_hybrid_rejects_cut_bound_to_another_assignment() {
        let model = separating_cut_model();
        let decomposition = admit(&model);
        let CertifiedHybridPbLpDecision::Infeasible(mut certificate) =
            try_solve_certified(&model, None).expect("certified hybrid result")
        else {
            panic!("expected certified infeasibility");
        };

        let (index, row) = certificate
            .cuts
            .iter()
            .enumerate()
            .find_map(|(index, cut)| match cut {
                HybridPbLpInfeasibilityCut::Certified { row, .. } => {
                    Some((index, row.to_row().expect("exact certified row")))
                }
                HybridPbLpInfeasibilityCut::NoGood { .. } => None,
            })
            .expect("the ledger must contain a certified projected row");

        // Find an assignment this row does NOT exclude. `cut_violated` is the
        // guard under test; asking it directly is how we know the tamper we are
        // about to apply is one it can see.
        let width = decomposition.master_to_original.len();
        assert!(width >= 2, "the fixture needs a multi-binary master");
        let spared = (0..1u32 << width)
            .map(|mask| (0..width).map(|bit| (mask >> bit) & 1 == 1).collect())
            .find(|candidate: &Vec<bool>| {
                !cut_violated(&row, &decomposition, candidate, None, &mut || false)
            })
            .expect(
                "VACUOUS TAMPER GUARD: this cut excludes EVERY master \
                 assignment, so rewriting its `assignment` cannot be detected \
                 and this test would pass while exercising nothing. That is \
                 exactly what the one-binary fixed-charge fixture did. Pick a \
                 model whose projected row separates only some assignments.",
            );

        match &mut certificate.cuts[index] {
            HybridPbLpInfeasibilityCut::Certified { assignment, .. } => *assignment = spared,
            HybridPbLpInfeasibilityCut::NoGood { .. } => unreachable!(),
        }
        assert_eq!(
            verify_hybrid_pb_lp_infeasibility_certificate(&model, &certificate),
            Err(HybridPbLpCertificateVerificationError::InvalidCutLedger),
            "a Farkas row credited to an assignment it does not cut off must be \
             rejected by the cut ledger"
        );
    }

    /// The load-bearing fields of a Certified cut's ROW, which `cut_violated`
    /// does not look at: `CertifiedRow::verify` must catch them.
    #[test]
    fn certified_hybrid_rejects_a_perturbed_projected_row() {
        for perturb_lb in [true, false] {
            let model = separating_cut_model();
            let CertifiedHybridPbLpDecision::Infeasible(mut certificate) =
                try_solve_certified(&model, None).expect("certified hybrid result")
            else {
                panic!("expected certified infeasibility");
            };
            let index = certificate
                .cuts
                .iter()
                .position(|cut| matches!(cut, HybridPbLpInfeasibilityCut::Certified { .. }))
                .expect("certified cut");
            match &mut certificate.cuts[index] {
                HybridPbLpInfeasibilityCut::Certified { row, .. } => {
                    if perturb_lb {
                        // Strengthen the bound past what the multipliers prove.
                        let inflated = row.lb.to_rational().expect("exact lb") + BigRational::one();
                        row.lb = HybridRational::from_rational(&inflated);
                    } else {
                        // Drop a multiplier: the row no longer follows.
                        assert!(
                            row.multipliers.len() >= 2,
                            "the projected row must combine at least two facts \
                             for this tamper to mean anything"
                        );
                        row.multipliers.pop();
                    }
                }
                HybridPbLpInfeasibilityCut::NoGood { .. } => unreachable!(),
            }
            assert_ne!(
                verify_hybrid_pb_lp_infeasibility_certificate(&model, &certificate),
                Ok(()),
                "a projected row that does not follow from its own multipliers \
                 must not be accepted (perturb_lb={perturb_lb})"
            );
        }
    }

    #[test]
    fn certified_hybrid_rejects_corrupt_final_master_refutation() {
        let model = fixed_charge_model(2.0);
        let CertifiedHybridPbLpDecision::Infeasible(mut certificate) =
            try_solve_certified(&model, None).expect("certified hybrid result")
        else {
            panic!("expected certified infeasibility");
        };
        certificate.master_refutation.format = "forged".to_owned();
        assert_eq!(
            verify_hybrid_pb_lp_infeasibility_certificate(&model, &certificate),
            Err(HybridPbLpCertificateVerificationError::MasterRefutationRejected)
        );
    }

    #[test]
    fn certified_hybrid_rejects_noncanonical_rational_wire_values() {
        let model = fixed_charge_model(2.0);
        let CertifiedHybridPbLpDecision::Infeasible(mut certificate) =
            try_solve_certified(&model, None).expect("certified hybrid result")
        else {
            panic!("expected certified infeasibility");
        };
        match certificate.cuts.first_mut().expect("learned cut") {
            HybridPbLpInfeasibilityCut::Certified { row, .. } => {
                row.lb.denominator = BigInt::zero();
            }
            HybridPbLpInfeasibilityCut::NoGood { farkas, .. } => {
                farkas.multipliers[0].coeff.denominator = BigInt::zero();
            }
        }
        let encoded = encode_hybrid_pb_lp_infeasibility_certificate_json(&certificate)
            .expect("malformed rational remains safely serializable data");
        let decoded = decode_hybrid_pb_lp_infeasibility_certificate_json(&encoded)
            .expect("wire decode does not construct an invalid BigRational");
        assert_eq!(
            verify_hybrid_pb_lp_infeasibility_certificate(&model, &decoded),
            Err(HybridPbLpCertificateVerificationError::InvalidCutLedger)
        );
    }

    #[test]
    fn certified_hybrid_codec_is_bounded_and_fail_closed() {
        let model = fixed_charge_model(2.0);
        let CertifiedHybridPbLpDecision::Infeasible(certificate) =
            try_solve_certified(&model, None).expect("certified hybrid result")
        else {
            panic!("expected certified infeasibility");
        };
        assert!(matches!(
            encode_hybrid_pb_lp_infeasibility_certificate_json_with_limit(&certificate, 1),
            Err(HybridPbLpCertificateCodecError::Oversized { limit: 1 })
        ));
        assert!(matches!(
            decode_hybrid_pb_lp_infeasibility_certificate_json(b"{\"format\":\"forged\"}"),
            Err(HybridPbLpCertificateCodecError::Malformed(_))
        ));
    }

    #[test]
    fn certified_hybrid_interruption_never_becomes_infeasibility() {
        let model = fixed_charge_model(2.0);
        assert!(try_solve_certified_interruptible(&model, None, || true).is_none());

        let CertifiedHybridPbLpDecision::Infeasible(certificate) =
            try_solve_certified(&model, None).expect("certified hybrid result")
        else {
            panic!("expected certified infeasibility");
        };
        assert_eq!(
            verify_hybrid_pb_lp_infeasibility_certificate_interruptible(
                &model,
                &certificate,
                None,
                &mut || true,
            ),
            Err(HybridPbLpCertificateVerificationError::Interrupted)
        );
    }

    #[test]
    fn hybrid_route_keeps_fractional_continuous_witness_exact() {
        let mut model = Model::new();
        let choose = model.add_binary_col();
        let amount = model.add_col(0.0, 1.0);
        model.add_row(0.5, 0.5, &[(amount, 1.0)]);
        // A genuine coupling row that is redundant but structural.
        model.add_row(f64::NEG_INFINITY, 1.0, &[(amount, 1.0), (choose, -1.0)]);
        model.add_row(1.0, 1.0, &[(choose, 1.0)]);
        model.set_objective(&[(choose, 1.0)], Sense::Minimize);

        let decision = try_solve(&model, None).expect("hybrid result");
        let HybridPbLpDecision::Optimal { model_values, .. } = decision else {
            panic!("expected optimum");
        };
        assert_eq!(model_values[1], BigRational::new(1.into(), 2.into()));
        model.check_point(&model_values).expect("exact witness");
    }

    #[test]
    fn admission_accepts_continuous_objective_but_declines_general_integer_master() {
        let mut continuous_cost = fixed_charge_model(1.0);
        continuous_cost.set_objective(&[(Col(0), 1.0), (Col(1), 1.0)], Sense::Minimize);
        let decomposition = Decomposition::admit(&continuous_cost, None, &mut || false)
            .expect("continuous recourse objective admitted");
        assert!(decomposition.has_continuous_objective);

        let mut general = Model::new();
        let integer = general.add_int_col(0.0, 2.0);
        let real = general.add_col(0.0, 2.0);
        general.add_row(1.0, f64::INFINITY, &[(integer, 1.0), (real, 1.0)]);
        assert!(Decomposition::admit(&general, None, &mut || false).is_none());
    }

    #[test]
    fn hybrid_route_proves_continuous_recourse_minimum() {
        let mut model = Model::new();
        let choose = model.add_binary_col();
        let recourse = model.add_col(0.0, 4.0);
        // recourse >= 4 - 3 choose
        model.add_row(4.0, f64::INFINITY, &[(recourse, 1.0), (choose, 3.0)]);
        model.set_objective(&[(choose, 2.0), (recourse, 1.0)], Sense::Minimize);
        let offset = BigRational::new(1.into(), 3.into());
        let offset_advice = offset.to_f64().expect("finite offset");
        model.set_objective_offset(offset_advice);
        model.record_inexact_obj_offset(offset);

        let decision = try_solve(&model, None).expect("hybrid result");
        let HybridPbLpDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected optimum");
        };
        assert_eq!(value, BigRational::new(10.into(), 3.into()));
        assert_eq!(model_values[choose.index()], integer(1));
        assert_eq!(model_values[recourse.index()], integer(1));
        assert_eq!(model.objective_value_at(&model_values), value);
        model.check_point(&model_values).expect("exact witness");
    }

    #[test]
    fn hybrid_route_proves_continuous_recourse_maximum_with_offset() {
        let mut model = Model::new();
        let choose = model.add_binary_col();
        let recourse = model.add_col(0.0, 3.0);
        // recourse <= 3 choose
        model.add_row(f64::NEG_INFINITY, 0.0, &[(recourse, 1.0), (choose, -3.0)]);
        model.set_objective(&[(choose, -1.0), (recourse, 1.0)], Sense::Maximize);
        let offset = BigRational::new(7.into(), 3.into());
        let offset_advice = offset.to_f64().expect("finite offset");
        model.set_objective_offset(offset_advice);
        model.record_inexact_obj_offset(offset);

        let decision = try_solve(&model, None).expect("hybrid result");
        let HybridPbLpDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected optimum");
        };
        assert_eq!(value, BigRational::new(13.into(), 3.into()));
        assert_eq!(model_values[choose.index()], integer(1));
        assert_eq!(model_values[recourse.index()], integer(3));
        assert_eq!(model.objective_value_at(&model_values), value);
        model.check_point(&model_values).expect("exact witness");
    }

    #[test]
    fn exact_side_store_continuous_objective_falls_back_to_exact_lp() {
        let mut model = Model::new();
        let choose = model.add_binary_col();
        let recourse = model.add_col(0.0, 2.0);
        // recourse >= 2 - 2 choose
        model.add_row(2.0, f64::INFINITY, &[(recourse, 1.0), (choose, 2.0)]);
        let third = BigRational::new(1.into(), 3.into());
        let advice = third.to_f64().expect("finite coefficient");
        model.set_objective(&[(choose, 1.0), (recourse, advice)], Sense::Minimize);
        model.record_inexact_obj_coeff(recourse.0, third.clone());

        let decision = try_solve(&model, None).expect("hybrid result");
        let HybridPbLpDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected optimum");
        };
        assert_eq!(value, &third * integer(2));
        assert_eq!(model_values[choose.index()], integer(0));
        assert_eq!(model_values[recourse.index()], integer(2));
        assert_eq!(model.objective_value_at(&model_values), value);
    }

    #[test]
    fn assignment_bound_optimum_must_project_to_an_original_model_row() {
        let mut model = Model::new();
        let choose = model.add_binary_col();
        let recourse = model.add_col(0.0, f64::INFINITY);
        let coupling = model.add_row(0.0, f64::INFINITY, &[(recourse, 1.0), (choose, -1.0)]);
        model.set_objective(&[(recourse, 1.0)], Sense::Minimize);
        let decomposition = admit(&model);
        let fixed = decomposition
            .fixed_model(&model, &[true], None, &mut || false)
            .expect("fixed model");
        let certificate = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(recourse.0, integer(1))],
            bound: integer(1),
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: coupling,
                        side: BoundSide::Lower,
                    },
                    coeff: integer(1),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: choose,
                        side: BoundSide::Lower,
                    },
                    coeff: integer(1),
                },
            ],
        };
        certificate
            .verify(&fixed)
            .expect("valid only under x = 1 assignment bounds");
        assert!(certificate
            .clone()
            .into_certified_row()
            .verify(&model)
            .is_err());

        let values = vec![integer(1), integer(1)];
        let projected = project_optimality_row(
            &model,
            &decomposition,
            &[true],
            &values,
            &certificate,
            None,
            &mut || false,
        )
        .expect("assignment fact removed and global row verified");
        assert_eq!(
            projected.coeffs,
            vec![(choose.0, integer(-1)), (recourse.0, integer(1))]
        );
        assert_eq!(projected.lb, integer(0));
        projected.verify(&model).expect("original-model proof");
        let cut = improvement_inequality(
            &model,
            &decomposition,
            &projected,
            &integer(1),
            None,
            &mut || false,
        )
        .expect("improvement cut");
        assert_eq!(
            pb_inequality_satisfied(&cut, &[true], None, &mut || false),
            Some(false)
        );
        assert_eq!(
            pb_inequality_satisfied(&cut, &[false], None, &mut || false),
            Some(true)
        );
    }

    #[test]
    fn no_good_license_rejects_a_farkas_from_another_assignment() {
        let model = fixed_charge_model(1.0);
        let decomposition = admit(&model);
        let mut checker = ContinuousSubproblem::new(&model, None, &mut || false).expect("LP");
        let SubproblemDecision::Infeasible(farkas) = checker
            .check(&model, &decomposition, &[false], None, &mut || false)
            .expect("subproblem result")
        else {
            panic!("closed arc must be infeasible");
        };
        let forged = CutLicense::NoGood {
            assignment: vec![true],
            farkas,
        };
        assert!(!forged.verify(&model, &decomposition, None, &mut || false));
    }

    #[test]
    fn hybrid_route_maps_max_objective_and_exact_offset() {
        let mut model = fixed_charge_model(0.0);
        model.set_objective(&[(Col(0), 3.0)], Sense::Maximize);
        let offset = BigRational::new(7.into(), 3.into());
        let offset_advice = offset.to_f64().expect("finite offset");
        model.set_objective_offset(offset_advice);
        if exact(offset_advice).as_ref() != Some(&offset) {
            model.record_inexact_obj_offset(offset.clone());
        }

        let decision = try_solve(&model, None).expect("hybrid result");
        let HybridPbLpDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected optimum");
        };
        assert_eq!(value, BigRational::new(16.into(), 3.into()));
        assert_eq!(model_values[0], integer(1));
        model.check_point(&model_values).expect("exact witness");
    }

    #[test]
    fn compact_mapping_preserves_interleaved_original_columns() {
        let mut model = Model::new();
        let first_flow = model.add_col(0.0, 1.0);
        let first_open = model.add_binary_col();
        let second_flow = model.add_col(0.0, 1.0);
        let second_open = model.add_binary_col();
        model.add_row(
            f64::NEG_INFINITY,
            0.0,
            &[(first_flow, 1.0), (first_open, -1.0)],
        );
        model.add_row(
            f64::NEG_INFINITY,
            0.0,
            &[(second_flow, 1.0), (second_open, -1.0)],
        );
        model.add_row(1.0, f64::INFINITY, &[(first_open, 1.0), (second_open, 1.0)]);

        let decomposition = admit(&model);
        assert_eq!(
            decomposition.master_to_original,
            vec![first_open, second_open]
        );
        assert_eq!(
            decomposition.original_to_master,
            vec![None, Some(Col(0)), None, Some(Col(1))]
        );
        let fixed = decomposition
            .fixed_model(&model, &[true, false], None, &mut || false)
            .expect("fixed model");
        assert_eq!(fixed.col_bounds(first_open), (1.0, 1.0));
        assert_eq!(fixed.col_bounds(second_open), (0.0, 0.0));
        assert_eq!(fixed.col_bounds(first_flow), (0.0, 1.0));
        assert_eq!(fixed.col_bounds(second_flow), (0.0, 1.0));
    }

    /// Build a valid fixed-assignment Farkas proof whose projected global row
    /// has an rhs outside i128 after denominator clearing.  The model records
    /// the tiny coupling coefficients in the exact side store; their f64s are
    /// advice only.
    fn inexpressible_projection() -> (Model, FarkasCertificate) {
        let mut model = Model::new();
        let first = model.add_binary_col();
        let second = model.add_binary_col();
        let flow = model.add_col(0.0, f64::INFINITY);
        let p = BigInt::one() << 70usize;
        let q = (BigInt::one() << 70usize) + BigInt::one();
        let a = rational(BigInt::one(), p);
        let b = rational(BigInt::one(), q);
        let a_advice = a.to_f64().expect("finite coefficient");
        let b_advice = b.to_f64().expect("finite coefficient");
        let coupling = model.add_row(
            f64::NEG_INFINITY,
            0.0,
            &[(flow, 1.0), (first, -a_advice), (second, -b_advice)],
        );
        model.record_inexact_row_coeff(coupling, first.0, -a.clone());
        model.record_inexact_row_coeff(coupling, second.0, -b.clone());
        let demand = model.add_row(1.0, f64::INFINITY, &[(flow, 1.0)]);

        let farkas = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: coupling,
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: demand,
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: first,
                        side: BoundSide::Upper,
                    },
                    coeff: a,
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: second,
                        side: BoundSide::Upper,
                    },
                    coeff: b,
                },
            ],
        };
        (model, farkas)
    }

    #[test]
    fn exact_side_store_projection_falls_back_to_licensed_no_good() {
        let (model, farkas) = inexpressible_projection();
        let decomposition = admit(&model);
        let fixed = decomposition
            .fixed_model(&model, &[false, false], None, &mut || false)
            .expect("fixed model");
        farkas.verify(&fixed).expect("valid leaf proof");
        let row = project_farkas_row(
            &model,
            &decomposition,
            &[false, false],
            &farkas,
            None,
            &mut || false,
        )
        .expect("projected row");
        assert_eq!(row.lb, integer(1));
        assert_eq!(row.coeffs.len(), 2);
        assert!(certified_cut_inequality(&decomposition, &row, None, &mut || false).is_none());

        let mut master = master_state(&decomposition);
        let initial_constraints = master.plan.num_constraints;
        let mut cuts = RetainedCuts::new(
            CutResourceLimits::production(),
            master.plan.constraints.len(),
        );
        decomposition
            .add_cut(
                &model,
                &[false, false],
                farkas,
                &mut master,
                &mut cuts,
                None,
                &mut || false,
            )
            .expect("licensed fallback");
        assert_eq!(master.plan.num_constraints, initial_constraints + 1);
        assert_eq!(master.instance.num_constraints, initial_constraints + 1);
        assert!(matches!(
            cuts.licenses.as_slice(),
            [CutLicense::NoGood { .. }]
        ));
        assert!(cuts.verify_all(&model, &decomposition, &master, None, &mut || false));
        let learned = master.plan.constraints.last().expect("learned no-good");
        assert_eq!(learned.terms, vec![(0, 1), (1, 1)]);
        assert_eq!(learned.rhs, 1);
    }

    #[test]
    fn certified_hybrid_serializes_assignment_farkas_no_goods() {
        let (model, _) = inexpressible_projection();
        let CertifiedHybridPbLpDecision::Infeasible(certificate) =
            try_solve_certified(&model, None).expect("certified hybrid result")
        else {
            panic!("expected certified infeasibility");
        };
        assert!(certificate
            .cuts
            .iter()
            .any(|cut| matches!(cut, HybridPbLpInfeasibilityCut::NoGood { .. })));
        verify_hybrid_pb_lp_infeasibility_certificate(&model, &certificate)
            .expect("assignment Farkas licenses and final master replay");
        let encoded = encode_hybrid_pb_lp_infeasibility_certificate_json(&certificate)
            .expect("bounded no-good artifact");
        let decoded = decode_hybrid_pb_lp_infeasibility_certificate_json(&encoded)
            .expect("decode no-good artifact");
        verify_hybrid_pb_lp_infeasibility_certificate(&model, &decoded)
            .expect("decoded no-good artifact");
    }

    #[test]
    fn retained_evidence_limit_declines_without_mutating_master() {
        let model = fixed_charge_model(1.0);
        let decomposition = admit(&model);
        let mut checker = ContinuousSubproblem::new(&model, None, &mut || false).expect("LP");
        let SubproblemDecision::Infeasible(farkas) = checker
            .check(&model, &decomposition, &[false], None, &mut || false)
            .expect("subproblem result")
        else {
            panic!("closed arc must be infeasible");
        };
        let mut master = master_state(&decomposition);
        let initial_plan = master.plan.num_constraints;
        let initial_core = master.instance.num_constraints;
        let mut cuts = RetainedCuts::new(
            CutResourceLimits {
                bytes: 0,
                assignment_values: usize::MAX,
                pb_terms: usize::MAX,
                exact_multipliers: usize::MAX,
            },
            master.plan.constraints.len(),
        );

        assert!(decomposition
            .add_cut(
                &model,
                &[false],
                farkas,
                &mut master,
                &mut cuts,
                None,
                &mut || false,
            )
            .is_none());
        assert_eq!(master.plan.num_constraints, initial_plan);
        assert_eq!(master.instance.num_constraints, initial_core);
        assert!(cuts.licenses.is_empty());
        assert_eq!(cuts.usage.bytes, 0);
    }

    #[test]
    fn interruptible_route_polls_non_send_callback_before_master_solve() {
        let model = fixed_charge_model(1.0);
        let mut polls = 0usize;
        let result = try_solve_interruptible(&model, None, || {
            polls += 1;
            polls >= 2
        });
        assert!(result.is_none());
        assert!(polls >= 2);
    }
}
