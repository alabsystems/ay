// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fail-closed PB/PBO JIT candidate profiling.
//!
//! This module only extracts deterministic metadata for future external code generation
//! lowering. It intentionally does not compile code, install native dispatch,
//! or depend on retired external backend paths.

use std::collections::{BTreeMap, BTreeSet};

use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel};

const PB_JIT_CONTRACT_VERSION: u32 = 1;
const DEFAULT_MIN_REPETITIONS: usize = 4;
const DEFAULT_MAX_TERMS: usize = 256;

/// The only backend family this PB contract may target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PbJitBackend {
    /// The typed MIR to EXTERNAL_CODEGEN backend.
    ExternalCodegenBackend,
}

/// Static PB kernel shape observed during profiling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PbKernelKind {
    /// Unit-weight disjunction: `l_1 + ... + l_n >= 1`.
    ClausePropagation,
    /// Unit-weight cardinality propagation: `l_1 + ... + l_n >= k`.
    UnitCardinalityPropagation,
    /// General weighted pseudo-Boolean propagation.
    WeightedPropagation,
}

impl PbKernelKind {
    /// Stable token for runner telemetry.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ClausePropagation => "clause",
            Self::UnitCardinalityPropagation => "unit_cardinality",
            Self::WeightedPropagation => "weighted",
        }
    }
}

/// Internal extraction thresholds.
///
/// This is not a user-facing knob. It exists so tests can exercise the contract
/// deterministically while the production default stays conservative.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PbJitExtractionPolicy {
    /// Minimum number of matching constraints before a shape can be extracted.
    pub min_repetitions: usize,
    /// Maximum normalized terms allowed in the first candidate contract.
    pub max_terms: usize,
}

impl Default for PbJitExtractionPolicy {
    fn default() -> Self {
        Self {
            min_repetitions: DEFAULT_MIN_REPETITIONS,
            max_terms: DEFAULT_MAX_TERMS,
        }
    }
}

/// Why extraction refused to produce a candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PbJitRejection {
    /// Checked i128 normalization or objective-bound accounting overflowed.
    ArithmeticOverflow,
    /// A PB literal could not be represented as a non-zero DIMACS `i32`.
    LiteralOutOfRange,
    /// No repeated safe shape passed the current extraction policy.
    NoRepeatedSafeShape,
}

impl PbJitRejection {
    /// Stable token for runner telemetry.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ArithmeticOverflow => "arithmetic_overflow",
            Self::LiteralOutOfRange => "literal_out_of_range",
            Self::NoRepeatedSafeShape => "no_repeated_safe_shape",
        }
    }
}

/// Deterministic profile for one repeated PB kernel shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbKernelShapeProfile {
    /// Kernel family.
    pub kind: PbKernelKind,
    /// Number of normalized terms in the shape.
    pub terms: usize,
    /// Normalized `>=` degree.
    pub degree: i128,
    /// Sorted normalized coefficient signature.
    pub coefficients: Vec<i128>,
    /// Number of constraints matching this exact shape.
    pub repetitions: usize,
    /// Source constraint indices matching this shape.
    pub constraint_indices: Vec<usize>,
}

/// Static profile for future PB/PBO JIT decisions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbJitProfile {
    /// Number of constraints inspected.
    pub total_constraints: usize,
    /// Number of `>=` constraints inspected.
    pub ge_constraints: usize,
    /// Number of equality constraints skipped by this first contract.
    pub equality_constraints: usize,
    /// Constraints skipped because they contain non-linear terms.
    pub nonlinear_constraints: usize,
    /// Constraints skipped because exact normalization made them trivial.
    pub trivial_constraints: usize,
    /// Constraints skipped because the normalized degree exceeds total weight.
    pub structurally_unsat_constraints: usize,
    /// Constraints skipped because repeated normalized literals need merging.
    pub duplicate_literal_constraints: usize,
    /// Repeated and singleton propagation shapes, sorted deterministically.
    pub shapes: Vec<PbKernelShapeProfile>,
    /// Optional PBO objective-bound update profile.
    pub objective_bound_update: Option<PboObjectiveBoundProfile>,
}

/// Exact objective-bound update shape for PBO instances.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PboObjectiveBoundProfile {
    /// Number of objective terms.
    pub terms: usize,
    /// Number of single-literal objective terms.
    pub single_lit_terms: usize,
    /// Number of unit-weight objective terms.
    pub unit_weight_terms: usize,
    /// Largest absolute coefficient that fits in i128.
    pub max_abs_coeff: i128,
    /// Sum of absolute objective coefficients, checked in i128 range.
    pub total_abs_weight: i128,
}

/// A metadata-only candidate for later external code generation lowering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbJitCandidate {
    /// Contract version for future artifact metadata.
    pub contract_version: u32,
    /// Backend family allowed by this contract.
    pub backend: PbJitBackend,
    /// Kernel family selected for extraction.
    pub kind: PbKernelKind,
    /// Number of normalized terms in the selected shape.
    pub terms: usize,
    /// Normalized `>=` degree.
    pub degree: i128,
    /// Sorted normalized coefficient signature.
    pub coefficients: Vec<i128>,
    /// Number of matching constraints observed.
    pub repetitions: usize,
    /// Source constraint indices covered by this candidate.
    pub constraint_indices: Vec<usize>,
    /// Future compiled artifacts must use exact i128 arithmetic semantics.
    pub exact_i64_arithmetic: bool,
    /// Future compiled artifacts must preserve the scalar/interpreter fallback.
    pub interpreter_fallback_required: bool,
    /// Whether this build has a solve-path native ABI for this kernel shape.
    ///
    /// Profile extraction still never executes code or increments solve-path
    /// application counters.
    pub generated_code_execution_allowed: bool,
    /// Future compiled artifacts must require the external code generation backend.
    pub external_codegen_backend_backend_required: bool,
}

/// Extraction result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PbJitExtraction {
    /// A metadata-only candidate contract was accepted.
    Candidate(PbJitCandidate),
    /// Extraction failed closed.
    Rejected(PbJitRejection),
}

/// Profile-only counters for PB/PBO JIT candidate reporting.
///
/// These counters describe whether the metadata contract found a future
/// external code generation candidate. They do not imply generated-code dispatch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbJitCandidateTelemetry {
    /// Number of profile attempts. Successful parses report one attempt.
    pub profile_attempts: u64,
    /// Number of deterministic kernel shapes profiled.
    pub profiled_candidates: u64,
    /// Number of metadata candidates selected for the future backend.
    pub selected_candidates: u64,
    /// Number of failed-closed extraction attempts.
    pub rejected_candidates: u64,
    /// Rejection reason when no candidate was selected.
    pub rejection_reason: Option<PbJitRejection>,
    /// Selected kernel family, when present.
    pub kernel_kind: Option<PbKernelKind>,
    /// Selected kernel term count, or zero when none was selected.
    pub kernel_terms: u64,
    /// Selected kernel repetitions, or zero when none was selected.
    pub kernel_repetitions: u64,
    /// PBO objective profile, when the input contains an objective.
    pub objective_profile: Option<PboObjectiveBoundProfile>,
    /// Competition gate application counter for PB/PBO candidate shapes.
    ///
    /// In profile-only mode this is the number of scalar constraints covered by
    /// the selected metadata candidate, not native-code executions.
    pub pb_pbo_candidate_applications: u64,
    /// PB solve-path external code generation native-helper executions validated against the
    /// scalar fallback.
    ///
    /// Profile extraction must keep this zero. Only a helper that runs inside
    /// PB solving on the real assignment/propagation state may increment it;
    /// mismatch must deopt/fail closed before reporting evidence.
    pub pb_native_code_helper_applications: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ShapeKey {
    kind: PbKernelKind,
    terms: usize,
    degree: i128,
    coefficients: Vec<i128>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NormalizedTerm {
    lit: i32,
    coeff: i128,
}

/// Profiles PB/PBO kernel shapes in an OPB instance.
///
/// This mirrors the propagator's clause/cardinality/weighted shape split, but
/// stays outside solver state so extraction can fail closed before any runtime
/// dispatch exists.
pub fn profile_jit_kernel_shapes(instance: &PbInstance) -> Result<PbJitProfile, PbJitRejection> {
    let mut builder = ProfileBuilder::default();

    for (idx, constraint) in instance.constraints.iter().enumerate() {
        builder.observe_constraint(idx, constraint)?;
    }

    let objective_bound_update = instance
        .objective
        .as_ref()
        .map(profile_objective_bound_update)
        .transpose()?;

    Ok(builder.finish(objective_bound_update))
}

/// Extracts the first safe PB JIT candidate using the default policy.
#[must_use]
pub fn extract_first_jit_candidate(instance: &PbInstance) -> PbJitExtraction {
    extract_first_jit_candidate_with_policy(instance, PbJitExtractionPolicy::default())
}

/// Extracts the first safe PB JIT candidate using an explicit internal policy.
#[must_use]
pub fn extract_first_jit_candidate_with_policy(
    instance: &PbInstance,
    policy: PbJitExtractionPolicy,
) -> PbJitExtraction {
    let profile = match profile_jit_kernel_shapes(instance) {
        Ok(profile) => profile,
        Err(reason) => return PbJitExtraction::Rejected(reason),
    };

    let Some(shape) = select_safe_propagation_candidate(&profile, policy) else {
        return PbJitExtraction::Rejected(PbJitRejection::NoRepeatedSafeShape);
    };

    PbJitExtraction::Candidate(candidate_from_shape(shape))
}

/// Builds profile-only telemetry for PB/PBO JIT candidate reporting.
#[must_use]
pub fn profile_jit_candidate_telemetry(instance: &PbInstance) -> PbJitCandidateTelemetry {
    profile_jit_candidate_telemetry_with_policy(instance, PbJitExtractionPolicy::default())
}

/// Builds profile-only telemetry using an explicit internal extraction policy.
#[must_use]
pub fn profile_jit_candidate_telemetry_with_policy(
    instance: &PbInstance,
    policy: PbJitExtractionPolicy,
) -> PbJitCandidateTelemetry {
    let profile = match profile_jit_kernel_shapes(instance) {
        Ok(profile) => profile,
        Err(reason) => {
            return PbJitCandidateTelemetry {
                profile_attempts: 1,
                profiled_candidates: 0,
                selected_candidates: 0,
                rejected_candidates: 1,
                rejection_reason: Some(reason),
                kernel_kind: None,
                kernel_terms: 0,
                kernel_repetitions: 0,
                objective_profile: None,
                pb_pbo_candidate_applications: 0,
                pb_native_code_helper_applications: 0,
            };
        }
    };

    if let Some(shape) = select_safe_propagation_candidate(&profile, policy) {
        return PbJitCandidateTelemetry {
            profile_attempts: 1,
            profiled_candidates: profile.shapes.len() as u64,
            selected_candidates: 1,
            rejected_candidates: 0,
            rejection_reason: None,
            kernel_kind: Some(shape.kind),
            kernel_terms: shape.terms as u64,
            kernel_repetitions: shape.repetitions as u64,
            objective_profile: profile.objective_bound_update,
            pb_pbo_candidate_applications: shape.repetitions as u64,
            pb_native_code_helper_applications: solve_path_native_helper_applications(),
        };
    }

    PbJitCandidateTelemetry {
        profile_attempts: 1,
        profiled_candidates: profile.shapes.len() as u64,
        selected_candidates: 0,
        rejected_candidates: 1,
        rejection_reason: Some(PbJitRejection::NoRepeatedSafeShape),
        kernel_kind: None,
        kernel_terms: 0,
        kernel_repetitions: 0,
        objective_profile: profile.objective_bound_update,
        pb_pbo_candidate_applications: 0,
        pb_native_code_helper_applications: 0,
    }
}

fn candidate_from_shape(shape: &PbKernelShapeProfile) -> PbJitCandidate {
    PbJitCandidate {
        contract_version: PB_JIT_CONTRACT_VERSION,
        backend: PbJitBackend::ExternalCodegenBackend,
        kind: shape.kind,
        terms: shape.terms,
        degree: shape.degree,
        coefficients: shape.coefficients.clone(),
        repetitions: shape.repetitions,
        constraint_indices: shape.constraint_indices.clone(),
        exact_i64_arithmetic: true,
        interpreter_fallback_required: true,
        generated_code_execution_allowed: generated_code_execution_allowed_for_shape(shape.kind),
        external_codegen_backend_backend_required: true,
    }
}

fn generated_code_execution_allowed_for_shape(kind: PbKernelKind) -> bool {
    false && matches!(kind, PbKernelKind::UnitCardinalityPropagation)
}

fn select_safe_propagation_candidate(
    profile: &PbJitProfile,
    policy: PbJitExtractionPolicy,
) -> Option<&PbKernelShapeProfile> {
    profile
        .shapes
        .iter()
        .filter(|shape| {
            matches!(
                shape.kind,
                PbKernelKind::ClausePropagation | PbKernelKind::UnitCardinalityPropagation
            ) && shape.repetitions >= policy.min_repetitions
                && shape.terms <= policy.max_terms
        })
        .max_by(|lhs, rhs| {
            candidate_rank(lhs)
                .cmp(&candidate_rank(rhs))
                .then_with(|| rhs.constraint_indices[0].cmp(&lhs.constraint_indices[0]))
        })
}

fn candidate_rank(shape: &PbKernelShapeProfile) -> (usize, u128, usize, i128) {
    let work = (shape.repetitions as u128) * (shape.terms as u128);
    (shape.repetitions, work, shape.terms, -shape.degree)
}

fn solve_path_native_helper_applications() -> u64 {
    // Next implementation hook: feed this from PB CDCL propagation after an
    // external code generation helper evaluates the live watched-slack/assignment state and
    // the scalar propagator agrees. Startup/profile extraction has no live
    // assignment state, so it must report zero.
    0
}

#[derive(Debug, Default)]
struct ProfileBuilder {
    total_constraints: usize,
    ge_constraints: usize,
    equality_constraints: usize,
    nonlinear_constraints: usize,
    trivial_constraints: usize,
    structurally_unsat_constraints: usize,
    duplicate_literal_constraints: usize,
    shapes: BTreeMap<ShapeKey, Vec<usize>>,
}

impl ProfileBuilder {
    fn observe_constraint(
        &mut self,
        idx: usize,
        constraint: &PbConstraint,
    ) -> Result<(), PbJitRejection> {
        self.total_constraints += 1;

        if constraint.rel != PbRel::Ge {
            self.equality_constraints += 1;
            return Ok(());
        }
        self.ge_constraints += 1;

        if constraint.terms.iter().any(|term| term.lits.len() > 1) {
            self.nonlinear_constraints += 1;
            return Ok(());
        }

        let Some((terms, degree)) = normalize_ge_constraint_checked(constraint)? else {
            self.trivial_constraints += 1;
            return Ok(());
        };

        if has_duplicate_literals(&terms) {
            self.duplicate_literal_constraints += 1;
            return Ok(());
        }

        let total_coeff = checked_total_coeff(&terms)?;
        if degree > total_coeff {
            self.structurally_unsat_constraints += 1;
            return Ok(());
        }

        let key = shape_key_for_terms(&terms, degree);
        self.shapes.entry(key).or_default().push(idx);
        Ok(())
    }

    fn finish(self, objective_bound_update: Option<PboObjectiveBoundProfile>) -> PbJitProfile {
        let shapes = self
            .shapes
            .into_iter()
            .map(|(key, constraint_indices)| PbKernelShapeProfile {
                kind: key.kind,
                terms: key.terms,
                degree: key.degree,
                coefficients: key.coefficients,
                repetitions: constraint_indices.len(),
                constraint_indices,
            })
            .collect();

        PbJitProfile {
            total_constraints: self.total_constraints,
            ge_constraints: self.ge_constraints,
            equality_constraints: self.equality_constraints,
            nonlinear_constraints: self.nonlinear_constraints,
            trivial_constraints: self.trivial_constraints,
            structurally_unsat_constraints: self.structurally_unsat_constraints,
            duplicate_literal_constraints: self.duplicate_literal_constraints,
            shapes,
            objective_bound_update,
        }
    }
}

fn normalize_ge_constraint_checked(
    constraint: &PbConstraint,
) -> Result<Option<(Vec<NormalizedTerm>, i128)>, PbJitRejection> {
    let mut degree = constraint.rhs;
    let mut normalized = Vec::new();

    for term in &constraint.terms {
        if term.coeff == 0 {
            continue;
        }

        match term.lits.as_slice() {
            [] => {
                degree = degree
                    .checked_sub(term.coeff)
                    .ok_or(PbJitRejection::ArithmeticOverflow)?;
            }
            [lit] => {
                let dimacs = pb_lit_to_dimacs_checked(*lit)?;
                if term.coeff > 0 {
                    normalized.push(NormalizedTerm {
                        lit: dimacs,
                        coeff: term.coeff,
                    });
                } else {
                    degree = degree
                        .checked_sub(term.coeff)
                        .ok_or(PbJitRejection::ArithmeticOverflow)?;
                    normalized.push(NormalizedTerm {
                        lit: -dimacs,
                        coeff: term
                            .coeff
                            .checked_neg()
                            .ok_or(PbJitRejection::ArithmeticOverflow)?,
                    });
                }
            }
            _ => unreachable!("non-linear terms are filtered before normalization"),
        }
    }

    if degree <= 0 {
        return Ok(None);
    }

    normalized.sort_unstable_by(|lhs, rhs| {
        rhs.coeff
            .cmp(&lhs.coeff)
            .then_with(|| lhs.lit.unsigned_abs().cmp(&rhs.lit.unsigned_abs()))
            .then_with(|| lhs.lit.cmp(&rhs.lit))
    });

    Ok(Some((normalized, degree)))
}

fn shape_key_for_terms(terms: &[NormalizedTerm], degree: i128) -> ShapeKey {
    let mut coefficients: Vec<i128> = terms.iter().map(|term| term.coeff).collect();
    coefficients.sort_unstable_by(|lhs, rhs| rhs.cmp(lhs));

    let kind = if coefficients.iter().all(|&coeff| coeff == 1) {
        if degree == 1 {
            PbKernelKind::ClausePropagation
        } else {
            PbKernelKind::UnitCardinalityPropagation
        }
    } else {
        PbKernelKind::WeightedPropagation
    };

    ShapeKey {
        kind,
        terms: terms.len(),
        degree,
        coefficients,
    }
}

fn checked_total_coeff(terms: &[NormalizedTerm]) -> Result<i128, PbJitRejection> {
    terms.iter().try_fold(0i128, |sum, term| {
        sum.checked_add(term.coeff)
            .ok_or(PbJitRejection::ArithmeticOverflow)
    })
}

fn has_duplicate_literals(terms: &[NormalizedTerm]) -> bool {
    let mut seen = BTreeSet::new();
    terms.iter().any(|term| !seen.insert(term.lit))
}

fn profile_objective_bound_update(
    objective: &PbObjective,
) -> Result<PboObjectiveBoundProfile, PbJitRejection> {
    let mut single_lit_terms = 0usize;
    let mut unit_weight_terms = 0usize;
    let mut max_abs_coeff = 0i128;
    let mut total_abs_weight = 0i128;

    for term in &objective.terms {
        if term.lits.len() == 1 {
            single_lit_terms += 1;
        }

        let abs_coeff = checked_abs_i64(term.coeff)?;
        if abs_coeff == 1 {
            unit_weight_terms += 1;
        }
        max_abs_coeff = max_abs_coeff.max(abs_coeff);
        total_abs_weight = total_abs_weight
            .checked_add(abs_coeff)
            .ok_or(PbJitRejection::ArithmeticOverflow)?;
    }

    Ok(PboObjectiveBoundProfile {
        terms: objective.terms.len(),
        single_lit_terms,
        unit_weight_terms,
        max_abs_coeff,
        total_abs_weight,
    })
}

fn checked_abs_i64(value: i128) -> Result<i128, PbJitRejection> {
    value
        .checked_abs()
        .ok_or(PbJitRejection::ArithmeticOverflow)
}

fn pb_lit_to_dimacs_checked(lit: PbLit) -> Result<i32, PbJitRejection> {
    if lit.var == 0 {
        return Err(PbJitRejection::LiteralOutOfRange);
    }

    let var = i32::try_from(lit.var).map_err(|_| PbJitRejection::LiteralOutOfRange)?;
    Ok(if lit.negated { -var } else { var })
}
