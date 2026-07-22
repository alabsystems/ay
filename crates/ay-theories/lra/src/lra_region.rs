// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRA-side integration for basis-local compiled-region metadata.
//!
//! This module is intentionally metadata-only. It records the last pivot-shaped
//! row neighborhood and turns it into a `ay_jit::LraBasisRegionRequest` only at
//! simplex/theory boundaries where the interpreted solver has already completed.

use super::*;
use crate::tableau::RowPrecision;

/// Maximum metadata-only basis-region requests retained by one solver.
pub(crate) const MAX_LRA_BASIS_REGION_REQUESTS: usize = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LraI64RowLoweringMetadata {
    pub(crate) row_idx: u32,
    pub(crate) basic_var: u32,
    pub(crate) coefficient_count: u32,
    pub(crate) constant: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LraBasisRegionI64LoweringMetadata {
    pub(crate) rows: Vec<ay_jit::LraRegionRowShape>,
    pub(crate) row_metadata: Vec<LraI64RowLoweringMetadata>,
    pub(crate) coefficient_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LraBasisRegionLoweringContract {
    I64FastExternalCodegenBackend(LraBasisRegionI64LoweringMetadata),
    InterpretedExact(LraBasisRegionExactReason),
}

impl LraBasisRegionLoweringContract {
    fn into_i64_runtime_payload(
        self,
        neighborhood: ay_jit::LraRegionNeighborhood,
    ) -> Result<ay_jit::LraBasisRegionRuntimePayload, LraBasisRegionExactReason> {
        match self {
            Self::I64FastExternalCodegenBackend(metadata) => {
                let LraBasisRegionI64LoweringMetadata {
                    rows,
                    row_metadata,
                    coefficient_count,
                } = metadata;
                debug_assert_eq!(row_metadata.len(), rows.len());
                debug_assert_eq!(
                    coefficient_count,
                    rows.iter().map(|row| row.coefficients.len()).sum::<usize>()
                );
                let runtime_rows = rows
                    .into_iter()
                    .zip(row_metadata)
                    .map(|(shape, metadata)| {
                        debug_assert_eq!(shape.row_idx, metadata.row_idx);
                        debug_assert_eq!(shape.basic_var, metadata.basic_var);
                        ay_jit::LraBasisRegionRuntimeRow::from_shape(shape, metadata.constant)
                    })
                    .collect();
                Ok(ay_jit::LraBasisRegionRuntimePayload::new(
                    neighborhood,
                    runtime_rows,
                ))
            }
            Self::InterpretedExact(reason) => Err(reason),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LraBasisRegionExactReason {
    MissingRow {
        row_idx: u32,
    },
    RegionRowsTooLarge {
        row_count: usize,
        max_rows: usize,
    },
    RegionCoefficientsTooLarge {
        coefficient_count: usize,
        max_coefficients: usize,
    },
    RowRequiresExact {
        row_idx: u32,
        reason: LraRowExactReason,
    },
}

impl LraBasisRegionExactReason {
    fn to_region_rejection(&self) -> ay_jit::LraRegionEligibilityRejection {
        match self {
            Self::MissingRow { .. } => {
                ay_jit::LraRegionEligibilityRejection::NeighborhoodRowsMismatch
            }
            Self::RegionRowsTooLarge { .. } | Self::RegionCoefficientsTooLarge { .. } => {
                ay_jit::LraRegionEligibilityRejection::RegionTooLarge
            }
            Self::RowRequiresExact { row_idx, .. } => {
                ay_jit::LraRegionEligibilityRejection::NonCanonicalCoefficients {
                    row_idx: *row_idx,
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LraRowExactReason {
    PrecisionNotI64 { precision: RowPrecision },
    ConstantNotI64Integer,
    CoefficientNotI64Integer { var: u32 },
    ZeroCoefficient { var: u32 },
    NonCanonicalCoefficientOrder,
    RowTooWide,
}

/// Pivot-shaped region candidate remembered until the next safe boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LraBasisRegionCandidate {
    root_row: u32,
    entering_var: u32,
    affected_rows: Vec<u32>,
}

impl LraSolver {
    /// Remember the row neighborhood from a pivot without constructing or
    /// enqueueing a compiled-region request in the pivot hot path.
    pub(crate) fn remember_lra_basis_region_candidate(
        &mut self,
        row_idx: usize,
        entering_var: u32,
        affected_rows: &[(usize, Option<usize>)],
    ) {
        self.lra_basis_region_candidate = None;
        let _ = (row_idx, entering_var, affected_rows);
    }

    /// Drop a pivot-region candidate when simplex did not reach a safe boundary.
    pub(crate) fn discard_lra_basis_region_candidate(&mut self) {
        self.lra_basis_region_candidate = None;
    }

    /// Construct and enqueue one metadata-only basis-region request at a safe
    /// LRA boundary. Any missing guard, runtime disable, unsupported row shape,
    /// or full queue fails closed by leaving the generic solver path unchanged.
    pub(crate) fn enqueue_lra_basis_region_request_at_safe_boundary(&mut self) {
        let Some(candidate) = self.lra_basis_region_candidate.take() else {
            return;
        };
        self.stats.lra_basis_region_boundary_checks += 1;

        if self.lra_basis_region_disabled_by_policy() {
            self.stats.lra_basis_region_disabled_skips += 1;
            return;
        }
        if self.lra_basis_region_requests.len() >= MAX_LRA_BASIS_REGION_REQUESTS {
            self.stats.lra_basis_region_queue_full_skips += 1;
            return;
        }

        match self.build_lra_basis_region_request(&candidate) {
            Ok(request) => {
                self.lra_basis_region_requests.push(request);
                self.stats.lra_basis_region_requests_queued += 1;
            }
            Err(_) => {
                self.stats.lra_basis_region_ineligible_skips += 1;
            }
        }
    }

    /// Submit the newest queued basis-region request to the background compiler
    /// at a solver-safe boundary. Older local requests are stale by construction
    /// and are dropped fail-closed before they can install.
    pub(crate) fn drain_lra_basis_region_requests_at_safe_boundary(&mut self) {
        let Some(request) = self.lra_basis_region_requests.pop() else {
            return;
        };
        self.lra_basis_region_requests.clear();

        if self.lra_basis_region_disabled_by_policy() {
            return;
        }

        if self
            .pivot_row_cache
            .submit_lra_basis_region_request(request)
        {}
    }

    fn lra_basis_region_disabled_by_policy(&self) -> bool {
        true
    }

    pub(crate) fn advance_lra_basis_region_basis_epoch(&mut self) {
        self.lra_basis_region_basis_epoch = self.lra_basis_region_basis_epoch.saturating_add(1);
    }

    fn build_lra_basis_region_request(
        &self,
        candidate: &LraBasisRegionCandidate,
    ) -> Result<ay_jit::LraBasisRegionRequest, ay_jit::LraRegionEligibilityRejection> {
        let neighborhood = ay_jit::LraRegionNeighborhood::substitute(
            candidate.root_row,
            candidate.entering_var,
            candidate.affected_rows.clone(),
        );
        let guards = ay_jit::LraRegionGuardMetadata::conservative();
        let runtime_payload = self
            .lra_basis_region_lowering_contract(candidate, guards)
            .into_i64_runtime_payload(neighborhood)
            .map_err(|reason| reason.to_region_rejection())?;
        ay_jit::LraBasisRegionRequest::try_new_with_runtime_payload(
            self.lra_basis_region_epochs(),
            runtime_payload,
            guards,
        )
    }

    fn lra_basis_region_lowering_contract(
        &self,
        candidate: &LraBasisRegionCandidate,
        guards: ay_jit::LraRegionGuardMetadata,
    ) -> LraBasisRegionLoweringContract {
        let row_ids = Self::lra_basis_region_row_ids(candidate);
        let max_rows = guards.max_region_rows as usize;
        if row_ids.len() > max_rows {
            return LraBasisRegionLoweringContract::InterpretedExact(
                LraBasisRegionExactReason::RegionRowsTooLarge {
                    row_count: row_ids.len(),
                    max_rows,
                },
            );
        }

        let max_coefficients = guards.max_region_coefficients as usize;
        let mut coefficient_count = 0usize;
        let mut rows = Vec::with_capacity(row_ids.len());
        let mut row_metadata = Vec::with_capacity(row_ids.len());
        for row_idx in row_ids {
            let idx = row_idx as usize;
            let Some(row) = self.rows.get(idx) else {
                return LraBasisRegionLoweringContract::InterpretedExact(
                    LraBasisRegionExactReason::MissingRow { row_idx },
                );
            };
            coefficient_count = match coefficient_count.checked_add(row.coeffs.len()) {
                Some(count) => count,
                None => {
                    return LraBasisRegionLoweringContract::InterpretedExact(
                        LraBasisRegionExactReason::RegionCoefficientsTooLarge {
                            coefficient_count: usize::MAX,
                            max_coefficients,
                        },
                    );
                }
            };
            if coefficient_count > max_coefficients {
                return LraBasisRegionLoweringContract::InterpretedExact(
                    LraBasisRegionExactReason::RegionCoefficientsTooLarge {
                        coefficient_count,
                        max_coefficients,
                    },
                );
            }

            match Self::lra_basis_region_i64_row_metadata(row_idx, row) {
                Ok((shape, metadata)) => {
                    rows.push(shape);
                    row_metadata.push(metadata);
                }
                Err(reason) => {
                    return LraBasisRegionLoweringContract::InterpretedExact(
                        LraBasisRegionExactReason::RowRequiresExact { row_idx, reason },
                    );
                }
            }
        }

        LraBasisRegionLoweringContract::I64FastExternalCodegenBackend(
            LraBasisRegionI64LoweringMetadata {
                rows,
                row_metadata,
                coefficient_count,
            },
        )
    }

    fn lra_basis_region_row_ids(candidate: &LraBasisRegionCandidate) -> Vec<u32> {
        let mut row_ids = Vec::with_capacity(candidate.affected_rows.len() + 1);
        row_ids.push(candidate.root_row);
        row_ids.extend(candidate.affected_rows.iter().copied());
        row_ids.sort_unstable();
        row_ids.dedup();
        row_ids
    }

    fn lra_basis_region_i64_row_metadata(
        row_idx: u32,
        row: &TableauRow,
    ) -> Result<(ay_jit::LraRegionRowShape, LraI64RowLoweringMetadata), LraRowExactReason> {
        if !matches!(row.precision(), RowPrecision::I64) {
            return Err(LraRowExactReason::PrecisionNotI64 {
                precision: row.precision(),
            });
        }
        let constant = row
            .constant
            .to_i64()
            .ok_or(LraRowExactReason::ConstantNotI64Integer)?;
        let coefficient_count =
            u32::try_from(row.coeffs.len()).map_err(|_| LraRowExactReason::RowTooWide)?;

        let mut coefficients = Vec::with_capacity(row.coeffs.len());
        let mut previous_var = None;
        for &(var, ref coeff) in &row.coeffs {
            if previous_var.is_some_and(|previous| previous >= var) {
                return Err(LraRowExactReason::NonCanonicalCoefficientOrder);
            }
            previous_var = Some(var);

            let coefficient = coeff
                .to_i64()
                .ok_or(LraRowExactReason::CoefficientNotI64Integer { var })?;
            if coefficient == 0 {
                return Err(LraRowExactReason::ZeroCoefficient { var });
            }
            coefficients.push((var, coefficient));
        }

        Ok((
            ay_jit::LraRegionRowShape::new(row_idx, row.basic_var, coefficients),
            LraI64RowLoweringMetadata {
                row_idx,
                basic_var: row.basic_var,
                coefficient_count,
                constant,
            },
        ))
    }

    fn lra_basis_region_epochs(&self) -> ay_jit::LraRegionEpochs {
        let config = u64::from(self.integer_mode)
            | (u64::from(ay_jit::no_external_codegen_backend_cached()) << 1);

        ay_jit::LraRegionEpochs {
            constraints: ((self.rows.len() as u64) << 32) ^ u64::from(self.next_var),
            theory_atoms: self.registered_atoms.len() as u64,
            basis: self.lra_basis_region_basis_epoch,
            trail: ((self.asserted_trail.len() as u64) << 32) ^ self.trail.len() as u64,
            config,
        }
    }
}
