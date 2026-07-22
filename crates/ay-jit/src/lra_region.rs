// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Basis-local LRA compiled-region metadata and bounded runtime payloads.
//!
//! This module describes a conservative basis-local region that an async
//! compiler may consume. It does not call a compiler, enqueue background work,
//! dispatch native code, or touch the active pivot path.

use serde::{Deserialize, Serialize};

use crate::solver_program::{
    GuardRequirements, InstallBoundarySet, InvalidationKey, SolverProgramGenerations,
    SolverProgramKind, SolverProgramProvenance,
};

/// Semantic version for basis-local LRA region normalization and lowering.
pub const LRA_BASIS_REGION_SEMANTIC_VERSION: u64 = 1;

/// Stable stats prefix for future basis-local LRA compiled-region counters.
pub const LRA_BASIS_REGION_STATS_PREFIX: &str = "solver_program.lra_basis_region";

const DEFAULT_MAX_REGION_ROWS: u32 = 32;
const DEFAULT_MAX_REGION_COEFFICIENTS: u32 = 1024;

const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// Mutable-state epochs captured by a basis-local LRA region request.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraRegionEpochs {
    /// Clause/constraint arena generation.
    pub constraints: u64,
    /// Theory atom table generation.
    pub theory_atoms: u64,
    /// Simplex/LRA basis generation.
    pub basis: u64,
    /// Trail or assignment generation.
    pub trail: u64,
    /// Runtime policy/configuration generation.
    pub config: u64,
}

impl LraRegionEpochs {
    /// Returns true when every captured epoch still matches the runtime epoch.
    #[must_use]
    pub fn is_valid_for(self, runtime: Self) -> bool {
        self == runtime
    }

    #[must_use]
    pub(crate) fn to_solver_program_generations(self) -> SolverProgramGenerations {
        SolverProgramGenerations {
            constraints: self.constraints,
            theory_atoms: self.theory_atoms,
            basis: self.basis,
            trail: self.trail,
            config: self.config,
        }
    }
}

/// Deterministic invalidation key for a basis-local LRA region.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraRegionInvalidationKey {
    /// Mutable state epochs captured at request time.
    pub epochs: LraRegionEpochs,
    /// Deterministic shape hash for rows and neighborhood topology.
    pub shape_hash: u64,
    /// Deterministic semantic hash for normalization/lowering policy.
    pub semantic_hash: u64,
}

impl LraRegionInvalidationKey {
    /// Returns true when this key is still valid for the runtime key.
    #[must_use]
    pub fn is_valid_for(self, runtime: Self) -> bool {
        self == runtime
    }

    #[must_use]
    pub(crate) fn to_solver_program_key(self) -> InvalidationKey {
        InvalidationKey {
            generations: self.epochs.to_solver_program_generations(),
            shape_hash: self.shape_hash,
            semantic_hash: self.semantic_hash,
        }
    }
}

/// Basis-local LRA region family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LraRegionNeighborhoodKind {
    /// Region around the pre-pivot row and the rows affected by that pivot.
    Pivot,
    /// Region around a post-pivot substitute row and rows that consume it.
    Substitute,
}

impl LraRegionNeighborhoodKind {
    #[must_use]
    const fn stable_tag(self) -> u64 {
        match self {
            Self::Pivot => 1,
            Self::Substitute => 2,
        }
    }
}

/// Basis-local row neighborhood considered for future region compilation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraRegionNeighborhood {
    /// Neighborhood family.
    pub kind: LraRegionNeighborhoodKind,
    /// Pivot/substitute root row.
    pub root_row: u32,
    /// Entering variable for the pivot or post-pivot substitute.
    pub entering_var: u32,
    /// Rows affected by the root row, sorted and excluding `root_row`.
    pub affected_rows: Vec<u32>,
}

impl LraRegionNeighborhood {
    /// Create metadata for a pre-pivot row neighborhood.
    #[must_use]
    pub fn pivot(root_row: u32, entering_var: u32, affected_rows: Vec<u32>) -> Self {
        Self {
            kind: LraRegionNeighborhoodKind::Pivot,
            root_row,
            entering_var,
            affected_rows,
        }
    }

    /// Create metadata for a post-pivot substitute neighborhood.
    #[must_use]
    pub fn substitute(root_row: u32, entering_var: u32, affected_rows: Vec<u32>) -> Self {
        Self {
            kind: LraRegionNeighborhoodKind::Substitute,
            root_row,
            entering_var,
            affected_rows,
        }
    }

    #[must_use]
    fn row_count(&self) -> usize {
        self.affected_rows.len().saturating_add(1)
    }
}

/// Canonical integer row shape captured for region identity.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraRegionRowShape {
    /// Index into the LRA tableau.
    pub row_idx: u32,
    /// Current basic variable for this row.
    pub basic_var: u32,
    /// Sorted non-zero integer coefficients for variables in this row.
    pub coefficients: Vec<(u32, i64)>,
}

impl LraRegionRowShape {
    /// Create a row-shape descriptor.
    #[must_use]
    pub fn new(row_idx: u32, basic_var: u32, coefficients: Vec<(u32, i64)>) -> Self {
        Self {
            row_idx,
            basic_var,
            coefficients,
        }
    }

    #[must_use]
    fn is_canonical(&self) -> bool {
        self.coefficients
            .iter()
            .all(|(_, coefficient)| *coefficient != 0)
            && self
                .coefficients
                .windows(2)
                .all(|pair| pair[0].0 < pair[1].0)
    }

    #[must_use]
    fn contains_var(&self, var: u32) -> bool {
        self.coefficients
            .binary_search_by_key(&var, |(candidate, _)| *candidate)
            .is_ok()
    }
}

/// Runtime row payload captured for a basis-local LRA region.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraBasisRegionRuntimeRow {
    /// Canonical row shape used for identity and lowering.
    pub shape: LraRegionRowShape,
    /// Current integer row constant.
    pub constant: i64,
}

impl LraBasisRegionRuntimeRow {
    /// Create a runtime row payload.
    #[must_use]
    pub fn new(row_idx: u32, basic_var: u32, constant: i64, coefficients: Vec<(u32, i64)>) -> Self {
        Self {
            shape: LraRegionRowShape::new(row_idx, basic_var, coefficients),
            constant,
        }
    }

    /// Create a runtime row payload from an already canonical shape.
    #[must_use]
    pub fn from_shape(shape: LraRegionRowShape, constant: i64) -> Self {
        Self { shape, constant }
    }
}

/// Typed runtime payload for a basis-local LRA region.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraBasisRegionRuntimePayload {
    /// Neighborhood covered by this region.
    pub neighborhood: LraRegionNeighborhood,
    /// Runtime rows captured at the safe boundary.
    pub rows: Vec<LraBasisRegionRuntimeRow>,
}

impl LraBasisRegionRuntimePayload {
    /// Create a typed runtime payload.
    #[must_use]
    pub fn new(neighborhood: LraRegionNeighborhood, rows: Vec<LraBasisRegionRuntimeRow>) -> Self {
        Self { neighborhood, rows }
    }

    #[must_use]
    pub(crate) fn row_shapes(&self) -> Vec<LraRegionRowShape> {
        self.rows.iter().map(|row| row.shape.clone()).collect()
    }

    /// Runtime evidence that must match before a compiled region can apply.
    pub fn runtime_evidence(
        &self,
    ) -> Result<LraBasisRegionRuntimeEvidence, LraRegionEligibilityRejection> {
        let rows = self.row_shapes();
        let validation_guards = LraRegionGuardMetadata {
            max_region_rows: u32::MAX,
            max_region_coefficients: u32::MAX,
            ..LraRegionGuardMetadata::conservative()
        };
        validate_neighborhood(&self.neighborhood, &rows, validation_guards)?;

        let row_count = u32::try_from(self.rows.len())
            .map_err(|_| LraRegionEligibilityRejection::RegionTooLarge)?;
        let coefficient_count_usize = self
            .rows
            .iter()
            .map(|row| row.shape.coefficients.len())
            .try_fold(0usize, usize::checked_add)
            .ok_or(LraRegionEligibilityRejection::RegionTooLarge)?;
        let coefficient_count = u32::try_from(coefficient_count_usize)
            .map_err(|_| LraRegionEligibilityRejection::RegionTooLarge)?;

        Ok(LraBasisRegionRuntimeEvidence {
            row_count,
            coefficient_count,
            row_evidence_hash: stable_runtime_row_evidence_hash(self),
        })
    }
}

/// Runtime row evidence for a guarded LRA basis-region apply attempt.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraBasisRegionRuntimeEvidence {
    /// Number of runtime rows supplied for the apply attempt.
    pub row_count: u32,
    /// Number of coefficients across all runtime rows.
    pub coefficient_count: u32,
    /// Deterministic hash of row identity, constants, and coefficients.
    pub row_evidence_hash: u64,
}

/// Conservative guard evidence captured before a region can be compiled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraRegionGuardMetadata {
    /// Runtime generations must be checked before applying the artifact.
    pub require_generation_match: bool,
    /// The generic LRA path must remain available for fallback.
    pub interpreter_fallback_available: bool,
    /// A differential/oracle check must be available before default-on use.
    pub oracle_check_available: bool,
    /// No compiled region frame may be active while installing/applying.
    pub no_active_compiled_frame: bool,
    /// Synchronous compilation is forbidden for this foundation slice.
    pub allow_synchronous_compile: bool,
    /// Conservative cap on the number of rows captured by one region.
    pub max_region_rows: u32,
    /// Conservative cap on all captured row coefficients.
    pub max_region_coefficients: u32,
}

impl LraRegionGuardMetadata {
    /// Fail-closed guard metadata for pre-production LRA regions.
    #[must_use]
    pub fn conservative() -> Self {
        Self {
            require_generation_match: true,
            interpreter_fallback_available: true,
            oracle_check_available: true,
            no_active_compiled_frame: true,
            allow_synchronous_compile: false,
            max_region_rows: DEFAULT_MAX_REGION_ROWS,
            max_region_coefficients: DEFAULT_MAX_REGION_COEFFICIENTS,
        }
    }

    /// Returns true when the guard metadata satisfies the conservative contract.
    #[must_use]
    pub fn satisfies_conservative_contract(self) -> bool {
        self.require_generation_match
            && self.interpreter_fallback_available
            && self.oracle_check_available
            && self.no_active_compiled_frame
            && !self.allow_synchronous_compile
    }

    #[must_use]
    pub(crate) fn to_solver_program_requirements(self) -> GuardRequirements {
        GuardRequirements {
            require_generation_match: self.require_generation_match,
            require_interpreter_fallback: self.interpreter_fallback_available,
            require_oracle_check: self.oracle_check_available,
        }
    }
}

/// Compile timing admitted by this metadata layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LraRegionCompileTiming {
    /// Region requests may only be handed to a future async/background compiler.
    BackgroundOnly,
}

/// Stable identity and profiling key for a basis-local LRA region.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LraBasisRegionProfileKey {
    /// Neighborhood family.
    pub kind: LraRegionNeighborhoodKind,
    /// Pivot/substitute root row.
    pub root_row: u32,
    /// Entering variable for this region.
    pub entering_var: u32,
    /// Basis generation captured at request time.
    pub basis_epoch: u64,
    /// Deterministic shape hash for rows and neighborhood topology.
    pub shape_hash: u64,
    /// Deterministic semantic hash for normalization/lowering policy.
    pub semantic_hash: u64,
}

impl LraBasisRegionProfileKey {
    /// Stable 64-bit hash for counters, snapshots, and artifact IDs.
    #[must_use]
    pub fn stable_hash(&self) -> u64 {
        let mut state = stable_hash_seed(b"ay.lra.basis_region.profile");
        stable_hash_u64(&mut state, self.kind.stable_tag());
        stable_hash_u64(&mut state, u64::from(self.root_row));
        stable_hash_u64(&mut state, u64::from(self.entering_var));
        stable_hash_u64(&mut state, self.basis_epoch);
        stable_hash_u64(&mut state, self.shape_hash);
        stable_hash_u64(&mut state, self.semantic_hash);
        state
    }

    /// Stable stats prefix shared by this artifact family.
    #[must_use]
    pub const fn stats_prefix(&self) -> &'static str {
        LRA_BASIS_REGION_STATS_PREFIX
    }
}

/// Metadata-only request for a future basis-local LRA compiled region.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LraBasisRegionRequest {
    /// Stable identity and profiling key.
    pub profile_key: LraBasisRegionProfileKey,
    /// Invalidation key compatible with the solver-program artifact contract.
    pub invalidation_key: LraRegionInvalidationKey,
    /// Guard evidence required before any compiled artifact may apply.
    pub guards: LraRegionGuardMetadata,
    /// Number of rows captured by the request.
    pub row_count: u32,
    /// Number of row coefficients captured by the request.
    pub coefficient_count: u32,
    /// Compile timing admitted by this request.
    pub compile_timing: LraRegionCompileTiming,
    /// Optional typed rows preserved for guarded runtime compilation.
    pub runtime_payload: Option<LraBasisRegionRuntimePayload>,
}

impl LraBasisRegionRequest {
    /// Build and validate a metadata-only request for a basis-local region.
    ///
    /// This performs deterministic hashing and conservative eligibility checks.
    /// It never calls code generation and never installs native code.
    pub fn try_new(
        epochs: LraRegionEpochs,
        neighborhood: LraRegionNeighborhood,
        rows: Vec<LraRegionRowShape>,
        guards: LraRegionGuardMetadata,
    ) -> Result<Self, LraRegionEligibilityRejection> {
        Self::try_new_inner(epochs, neighborhood, rows, guards, None)
    }

    /// Build and validate a request with a typed runtime payload.
    pub fn try_new_with_runtime_payload(
        epochs: LraRegionEpochs,
        runtime_payload: LraBasisRegionRuntimePayload,
        guards: LraRegionGuardMetadata,
    ) -> Result<Self, LraRegionEligibilityRejection> {
        let neighborhood = runtime_payload.neighborhood.clone();
        let rows = runtime_payload.row_shapes();
        Self::try_new_inner(epochs, neighborhood, rows, guards, Some(runtime_payload))
    }

    fn try_new_inner(
        epochs: LraRegionEpochs,
        neighborhood: LraRegionNeighborhood,
        rows: Vec<LraRegionRowShape>,
        guards: LraRegionGuardMetadata,
        runtime_payload: Option<LraBasisRegionRuntimePayload>,
    ) -> Result<Self, LraRegionEligibilityRejection> {
        validate_guards(guards)?;
        validate_neighborhood(&neighborhood, &rows, guards)?;

        let row_count =
            u32::try_from(rows.len()).map_err(|_| LraRegionEligibilityRejection::RegionTooLarge)?;
        let coefficient_count_usize = rows
            .iter()
            .map(|row| row.coefficients.len())
            .try_fold(0usize, usize::checked_add)
            .ok_or(LraRegionEligibilityRejection::RegionTooLarge)?;
        let coefficient_count = u32::try_from(coefficient_count_usize)
            .map_err(|_| LraRegionEligibilityRejection::RegionTooLarge)?;

        let shape_hash = stable_shape_hash(&neighborhood, &rows);
        let semantic_hash = stable_semantic_hash(neighborhood.kind);
        let profile_key = LraBasisRegionProfileKey {
            kind: neighborhood.kind,
            root_row: neighborhood.root_row,
            entering_var: neighborhood.entering_var,
            basis_epoch: epochs.basis,
            shape_hash,
            semantic_hash,
        };

        Ok(Self {
            profile_key,
            invalidation_key: LraRegionInvalidationKey {
                epochs,
                shape_hash,
                semantic_hash,
            },
            guards,
            row_count,
            coefficient_count,
            compile_timing: LraRegionCompileTiming::BackgroundOnly,
            runtime_payload,
        })
    }

    /// Whether this request is still metadata-only, with no runtime rows.
    #[must_use]
    pub const fn is_metadata_only(&self) -> bool {
        self.runtime_payload.is_none()
    }

    /// Runtime rows preserved for guarded background compilation.
    #[must_use]
    pub fn runtime_payload(&self) -> Option<&LraBasisRegionRuntimePayload> {
        self.runtime_payload.as_ref()
    }

    #[must_use]
    pub(crate) const fn solver_program_kind(&self) -> SolverProgramKind {
        SolverProgramKind::LraBasisRegion
    }

    #[must_use]
    pub(crate) fn solver_program_provenance(&self) -> SolverProgramProvenance {
        SolverProgramProvenance::LraBasisRegion {
            basis_generation: self.invalidation_key.epochs.basis,
        }
    }

    #[must_use]
    pub(crate) fn solver_program_invalidation_key(&self) -> InvalidationKey {
        self.invalidation_key.to_solver_program_key()
    }

    #[must_use]
    pub(crate) fn solver_program_guard_requirements(&self) -> GuardRequirements {
        self.guards.to_solver_program_requirements()
    }

    #[must_use]
    pub(crate) fn solver_program_install_boundaries(&self) -> InstallBoundarySet {
        InstallBoundarySet::restart_only()
    }
}

/// Conservative reason a candidate region cannot be compiled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LraRegionEligibilityRejection {
    /// Runtime generation matching was not captured.
    MissingGenerationGuard,
    /// Generic LRA fallback was unavailable.
    MissingInterpreterFallback,
    /// Differential/oracle validation was unavailable.
    MissingOracleCheck,
    /// A compiled region frame was already active.
    ActiveCompiledFrame,
    /// The caller attempted to permit synchronous compilation.
    SynchronousCompileForbidden,
    /// The region did not include any affected row beyond the root row.
    EmptyNeighborhood,
    /// Row list did not match root plus affected rows.
    NeighborhoodRowsMismatch,
    /// Rows were not sorted by row index or contained duplicates.
    NonCanonicalRows,
    /// A row had unsorted, duplicate, or zero coefficients.
    NonCanonicalCoefficients { row_idx: u32 },
    /// Pivot neighborhood did not contain the entering variable in the root row.
    PivotEnteringVarAbsent,
    /// Substitute neighborhood root row was not basic on the entering variable.
    SubstituteRootNotEnteringBasic,
    /// Conservative row or coefficient budget was exceeded.
    RegionTooLarge,
}

fn validate_guards(guards: LraRegionGuardMetadata) -> Result<(), LraRegionEligibilityRejection> {
    if !guards.require_generation_match {
        return Err(LraRegionEligibilityRejection::MissingGenerationGuard);
    }
    if !guards.interpreter_fallback_available {
        return Err(LraRegionEligibilityRejection::MissingInterpreterFallback);
    }
    if !guards.oracle_check_available {
        return Err(LraRegionEligibilityRejection::MissingOracleCheck);
    }
    if !guards.no_active_compiled_frame {
        return Err(LraRegionEligibilityRejection::ActiveCompiledFrame);
    }
    if guards.allow_synchronous_compile {
        return Err(LraRegionEligibilityRejection::SynchronousCompileForbidden);
    }
    Ok(())
}

fn validate_neighborhood(
    neighborhood: &LraRegionNeighborhood,
    rows: &[LraRegionRowShape],
    guards: LraRegionGuardMetadata,
) -> Result<(), LraRegionEligibilityRejection> {
    if neighborhood.affected_rows.is_empty() {
        return Err(LraRegionEligibilityRejection::EmptyNeighborhood);
    }
    if !is_strictly_sorted(&neighborhood.affected_rows)
        || neighborhood
            .affected_rows
            .binary_search(&neighborhood.root_row)
            .is_ok()
    {
        return Err(LraRegionEligibilityRejection::NeighborhoodRowsMismatch);
    }
    if rows.len() != neighborhood.row_count() || !rows_are_strictly_sorted(rows) {
        return Err(LraRegionEligibilityRejection::NonCanonicalRows);
    }

    let max_rows = usize::try_from(guards.max_region_rows)
        .map_err(|_| LraRegionEligibilityRejection::RegionTooLarge)?;
    if rows.len() > max_rows {
        return Err(LraRegionEligibilityRejection::RegionTooLarge);
    }

    let mut coefficient_count = 0usize;
    for row in rows {
        if !row.is_canonical() {
            return Err(LraRegionEligibilityRejection::NonCanonicalCoefficients {
                row_idx: row.row_idx,
            });
        }
        coefficient_count = coefficient_count
            .checked_add(row.coefficients.len())
            .ok_or(LraRegionEligibilityRejection::RegionTooLarge)?;
    }

    let max_coefficients = usize::try_from(guards.max_region_coefficients)
        .map_err(|_| LraRegionEligibilityRejection::RegionTooLarge)?;
    if coefficient_count > max_coefficients {
        return Err(LraRegionEligibilityRejection::RegionTooLarge);
    }

    let root = rows
        .binary_search_by_key(&neighborhood.root_row, |row| row.row_idx)
        .ok()
        .map(|idx| &rows[idx])
        .ok_or(LraRegionEligibilityRejection::NeighborhoodRowsMismatch)?;

    for affected_row in &neighborhood.affected_rows {
        if rows
            .binary_search_by_key(affected_row, |row| row.row_idx)
            .is_err()
        {
            return Err(LraRegionEligibilityRejection::NeighborhoodRowsMismatch);
        }
    }

    match neighborhood.kind {
        LraRegionNeighborhoodKind::Pivot if !root.contains_var(neighborhood.entering_var) => {
            Err(LraRegionEligibilityRejection::PivotEnteringVarAbsent)
        }
        LraRegionNeighborhoodKind::Substitute if root.basic_var != neighborhood.entering_var => {
            Err(LraRegionEligibilityRejection::SubstituteRootNotEnteringBasic)
        }
        _ => Ok(()),
    }
}

fn rows_are_strictly_sorted(rows: &[LraRegionRowShape]) -> bool {
    rows.windows(2)
        .all(|pair| pair[0].row_idx < pair[1].row_idx)
}

fn is_strictly_sorted(values: &[u32]) -> bool {
    values.windows(2).all(|pair| pair[0] < pair[1])
}

fn stable_semantic_hash(kind: LraRegionNeighborhoodKind) -> u64 {
    let mut state = stable_hash_seed(b"ay.lra.basis_region.semantic");
    stable_hash_u64(&mut state, LRA_BASIS_REGION_SEMANTIC_VERSION);
    stable_hash_u64(&mut state, kind.stable_tag());
    state
}

fn stable_shape_hash(neighborhood: &LraRegionNeighborhood, rows: &[LraRegionRowShape]) -> u64 {
    let mut state = stable_hash_seed(b"ay.lra.basis_region.shape");
    stable_hash_u64(&mut state, neighborhood.kind.stable_tag());
    stable_hash_u64(&mut state, u64::from(neighborhood.root_row));
    stable_hash_u64(&mut state, u64::from(neighborhood.entering_var));
    stable_hash_u64(&mut state, neighborhood.affected_rows.len() as u64);
    for row_idx in &neighborhood.affected_rows {
        stable_hash_u64(&mut state, u64::from(*row_idx));
    }
    stable_hash_u64(&mut state, rows.len() as u64);
    for row in rows {
        stable_hash_u64(&mut state, u64::from(row.row_idx));
        stable_hash_u64(&mut state, u64::from(row.basic_var));
        stable_hash_u64(&mut state, row.coefficients.len() as u64);
        for (var, coeff) in &row.coefficients {
            stable_hash_u64(&mut state, u64::from(*var));
            stable_hash_i64(&mut state, *coeff);
        }
    }
    state
}

fn stable_runtime_row_evidence_hash(payload: &LraBasisRegionRuntimePayload) -> u64 {
    let mut state = stable_hash_seed(b"ay.lra.basis_region.runtime_row_evidence");
    stable_hash_u64(&mut state, LRA_BASIS_REGION_SEMANTIC_VERSION);
    stable_hash_u64(&mut state, payload.neighborhood.kind.stable_tag());
    stable_hash_u64(&mut state, u64::from(payload.neighborhood.root_row));
    stable_hash_u64(&mut state, u64::from(payload.neighborhood.entering_var));
    stable_hash_u64(&mut state, payload.neighborhood.affected_rows.len() as u64);
    for row_idx in &payload.neighborhood.affected_rows {
        stable_hash_u64(&mut state, u64::from(*row_idx));
    }
    stable_hash_u64(&mut state, payload.rows.len() as u64);
    for row in &payload.rows {
        stable_hash_u64(&mut state, u64::from(row.shape.row_idx));
        stable_hash_u64(&mut state, u64::from(row.shape.basic_var));
        stable_hash_i64(&mut state, row.constant);
        stable_hash_u64(&mut state, row.shape.coefficients.len() as u64);
        for (var, coeff) in &row.shape.coefficients {
            stable_hash_u64(&mut state, u64::from(*var));
            stable_hash_i64(&mut state, *coeff);
        }
    }
    state
}

fn stable_hash_seed(domain: &[u8]) -> u64 {
    let mut state = FNV_OFFSET_BASIS;
    stable_hash_bytes(&mut state, domain);
    state
}

fn stable_hash_bytes(state: &mut u64, bytes: &[u8]) {
    stable_hash_u64(state, bytes.len() as u64);
    for byte in bytes {
        *state ^= u64::from(*byte);
        *state = state.wrapping_mul(FNV_PRIME);
    }
}

fn stable_hash_u64(state: &mut u64, value: u64) {
    for byte in value.to_le_bytes() {
        *state ^= u64::from(byte);
        *state = state.wrapping_mul(FNV_PRIME);
    }
}

fn stable_hash_i64(state: &mut u64, value: i64) {
    for byte in value.to_le_bytes() {
        *state ^= u64::from(byte);
        *state = state.wrapping_mul(FNV_PRIME);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn epochs() -> LraRegionEpochs {
        LraRegionEpochs {
            constraints: 10,
            theory_atoms: 11,
            basis: 12,
            trail: 13,
            config: 14,
        }
    }

    fn substitute_neighborhood() -> LraRegionNeighborhood {
        LraRegionNeighborhood::substitute(7, 13, vec![8, 9])
    }

    fn substitute_rows() -> Vec<LraRegionRowShape> {
        vec![
            LraRegionRowShape::new(7, 13, vec![(1, 5), (3, -2)]),
            LraRegionRowShape::new(8, 21, vec![(13, 1), (20, 4)]),
            LraRegionRowShape::new(9, 34, vec![(2, -7), (13, 3)]),
        ]
    }

    fn request() -> LraBasisRegionRequest {
        LraBasisRegionRequest::try_new(
            epochs(),
            substitute_neighborhood(),
            substitute_rows(),
            LraRegionGuardMetadata::conservative(),
        )
        .expect("valid basis-local region")
    }

    fn runtime_request() -> LraBasisRegionRequest {
        let payload = LraBasisRegionRuntimePayload::new(
            substitute_neighborhood(),
            vec![
                LraBasisRegionRuntimeRow::new(7, 13, 11, vec![(1, 5), (3, -2)]),
                LraBasisRegionRuntimeRow::new(8, 21, 17, vec![(13, 1), (20, 4)]),
                LraBasisRegionRuntimeRow::new(9, 34, 19, vec![(2, -7), (13, 3)]),
            ],
        );
        LraBasisRegionRequest::try_new_with_runtime_payload(
            epochs(),
            payload,
            LraRegionGuardMetadata::conservative(),
        )
        .expect("valid basis-local runtime region")
    }

    #[test]
    fn profile_key_hash_and_equality_are_stable() {
        let first = request().profile_key;
        let second = request().profile_key;
        assert_eq!(first, second);
        assert_eq!(first.stable_hash(), second.stable_hash());
        assert_eq!(first.shape_hash, 0x9c7f_7fb8_4894_368b);
        assert_eq!(first.semantic_hash, 0xb6a8_0a60_148c_a776);
        assert_eq!(first.stable_hash(), 0x4e3a_2cfe_767a_065f);
        assert_eq!(first.stats_prefix(), LRA_BASIS_REGION_STATS_PREFIX);

        let mut newer_epochs = epochs();
        newer_epochs.basis += 1;
        let newer_basis = LraBasisRegionRequest::try_new(
            newer_epochs,
            substitute_neighborhood(),
            substitute_rows(),
            LraRegionGuardMetadata::conservative(),
        )
        .expect("valid basis-local region")
        .profile_key;

        assert_ne!(first, newer_basis);
        assert_ne!(first.stable_hash(), newer_basis.stable_hash());
    }

    #[test]
    fn guard_rejects_missing_fallback_and_noncanonical_rows() {
        let missing_fallback = LraRegionGuardMetadata {
            interpreter_fallback_available: false,
            ..LraRegionGuardMetadata::conservative()
        };
        assert_eq!(
            LraBasisRegionRequest::try_new(
                epochs(),
                substitute_neighborhood(),
                substitute_rows(),
                missing_fallback,
            ),
            Err(LraRegionEligibilityRejection::MissingInterpreterFallback)
        );

        let noncanonical_rows = vec![
            LraRegionRowShape::new(7, 13, vec![(3, -2), (1, 5)]),
            LraRegionRowShape::new(8, 21, vec![(13, 1), (20, 4)]),
            LraRegionRowShape::new(9, 34, vec![(2, -7), (13, 3)]),
        ];
        assert_eq!(
            LraBasisRegionRequest::try_new(
                epochs(),
                substitute_neighborhood(),
                noncanonical_rows,
                LraRegionGuardMetadata::conservative(),
            ),
            Err(LraRegionEligibilityRejection::NonCanonicalCoefficients { row_idx: 7 })
        );
    }

    #[test]
    fn kind_specific_guards_reject_ineligible_neighborhoods() {
        assert_eq!(
            LraBasisRegionRequest::try_new(
                epochs(),
                LraRegionNeighborhood::substitute(7, 99, vec![8, 9]),
                substitute_rows(),
                LraRegionGuardMetadata::conservative(),
            ),
            Err(LraRegionEligibilityRejection::SubstituteRootNotEnteringBasic)
        );

        let pivot_rows = vec![
            LraRegionRowShape::new(7, 55, vec![(1, 5), (3, -2)]),
            LraRegionRowShape::new(8, 21, vec![(13, 1), (20, 4)]),
        ];
        assert_eq!(
            LraBasisRegionRequest::try_new(
                epochs(),
                LraRegionNeighborhood::pivot(7, 13, vec![8]),
                pivot_rows,
                LraRegionGuardMetadata::conservative(),
            ),
            Err(LraRegionEligibilityRejection::PivotEnteringVarAbsent)
        );
    }

    #[test]
    fn invalidation_key_matches_solver_program_contract() {
        let request = request();
        let runtime_key = request.invalidation_key;
        assert!(request.invalidation_key.is_valid_for(runtime_key));

        let stale_basis_key = LraRegionInvalidationKey {
            epochs: LraRegionEpochs {
                basis: runtime_key.epochs.basis + 1,
                ..runtime_key.epochs
            },
            ..runtime_key
        };
        assert!(!request.invalidation_key.is_valid_for(stale_basis_key));

        let solver_key = request.solver_program_invalidation_key();
        assert_eq!(
            solver_key.generations,
            SolverProgramGenerations {
                constraints: epochs().constraints,
                theory_atoms: epochs().theory_atoms,
                basis: epochs().basis,
                trail: epochs().trail,
                config: epochs().config,
            }
        );
        assert_eq!(solver_key.shape_hash, request.invalidation_key.shape_hash);
        assert_eq!(
            solver_key.semantic_hash,
            request.invalidation_key.semantic_hash
        );
        assert_eq!(
            request.solver_program_kind(),
            SolverProgramKind::LraBasisRegion
        );
        assert_eq!(
            request.solver_program_provenance(),
            SolverProgramProvenance::LraBasisRegion {
                basis_generation: epochs().basis,
            }
        );
        assert_eq!(
            request.solver_program_guard_requirements(),
            GuardRequirements::conservative()
        );
        assert!(request
            .solver_program_install_boundaries()
            .allows(crate::solver_program::InstallBoundary::Restart));
    }

    #[test]
    fn request_building_is_metadata_only_and_rejects_sync_compile() {
        let request = request();
        assert!(request.is_metadata_only());
        assert!(request.runtime_payload().is_none());
        assert_eq!(
            request.compile_timing,
            LraRegionCompileTiming::BackgroundOnly
        );
        assert!(!request.guards.allow_synchronous_compile);
        assert!(request.guards.satisfies_conservative_contract());

        let sync_guards = LraRegionGuardMetadata {
            allow_synchronous_compile: true,
            ..LraRegionGuardMetadata::conservative()
        };
        assert_eq!(
            LraBasisRegionRequest::try_new(
                epochs(),
                substitute_neighborhood(),
                substitute_rows(),
                sync_guards,
            ),
            Err(LraRegionEligibilityRejection::SynchronousCompileForbidden)
        );
    }

    #[test]
    fn runtime_payload_preserves_rows_and_keeps_stable_identity() {
        let metadata = request();
        let runtime = runtime_request();

        assert!(!runtime.is_metadata_only());
        assert_eq!(runtime.profile_key, metadata.profile_key);
        assert_eq!(runtime.invalidation_key, metadata.invalidation_key);
        assert_eq!(runtime.row_count, 3);
        assert_eq!(runtime.coefficient_count, 6);

        let payload = runtime.runtime_payload().expect("runtime payload");
        assert_eq!(payload.neighborhood, substitute_neighborhood());
        assert_eq!(payload.rows[0].constant, 11);
        assert_eq!(payload.rows[2].shape.row_idx, 9);
        assert_eq!(payload.rows[2].shape.coefficients, vec![(2, -7), (13, 3)]);
    }

    #[test]
    fn runtime_row_evidence_distinguishes_same_shape_constants() {
        let runtime = runtime_request();
        let payload = runtime.runtime_payload().expect("runtime payload");
        let evidence = payload
            .runtime_evidence()
            .expect("runtime evidence should be valid");
        assert_eq!(evidence.row_count, 3);
        assert_eq!(evidence.coefficient_count, 6);

        let mut stale_payload = payload.clone();
        stale_payload.rows[1].constant += 1;
        let stale_request = LraBasisRegionRequest::try_new_with_runtime_payload(
            epochs(),
            stale_payload.clone(),
            LraRegionGuardMetadata::conservative(),
        )
        .expect("stale payload shape should still be request-valid");
        let stale_evidence = stale_payload
            .runtime_evidence()
            .expect("stale runtime evidence should be valid");

        assert_eq!(runtime.profile_key, stale_request.profile_key);
        assert_eq!(runtime.invalidation_key, stale_request.invalidation_key);
        assert_ne!(evidence.row_evidence_hash, stale_evidence.row_evidence_hash);
    }
}
