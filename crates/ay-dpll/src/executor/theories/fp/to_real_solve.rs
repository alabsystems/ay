// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One stop owner across FP-to-Real encoding, nested solves and publication.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{CnfClause, TermId};
use ay_fp::{FpBuildProgress, FpModel};
use ay_sat::SatResult;

use crate::executor_types::{ExecutorError, Result, SolveResult, UnknownOrigin, UnknownReason};

use super::super::super::Executor;
use super::bitblast::FpRealEncodingError;
use super::stop::FpStop;
use super::to_real::{FpEncoding, FpRefinementStep};

mod mixed;
mod refinement;
mod sat_instance;
mod simple;
mod targets;
#[cfg(test)]
mod tests;

/// Private observations expose actual phase boundaries, not solver options.
#[derive(Clone, Copy, Debug)]
pub(super) enum FpRealPhase {
    Tseitin,
    Construction(FpBuildProgress),
    CongruenceScan,
    CongruencePlan,
    ClauseTransfer,
    EncodingReady,
    SatLoad,
    TargetedSearch,
    RefinementSearch,
    SimpleSearch,
    SatPoll,
    SatReturned,
    ModelExtracted,
    MixedCheckpoint,
    MixedChild,
    MixedRestored,
    Rewrite,
    TargetPreparation,
    Publication,
}

#[derive(Debug, thiserror::Error)]
pub(super) enum FpRealError {
    #[error("FP-to-Real attempt stopped: {0:?}")]
    Stopped(UnknownOrigin),
    #[error(transparent)]
    Executor(#[from] ExecutorError),
    #[error("unsupported FP predicate")]
    Unsupported,
    #[error("unresolved FP encoding condition")]
    EncodingGap,
    #[error("FP SAT assignment has no complete well-formed typed model")]
    ModelDecode,
}

impl From<FpRealEncodingError> for FpRealError {
    fn from(error: FpRealEncodingError) -> Self {
        match error {
            FpRealEncodingError::Stopped(origin) => Self::Stopped(origin),
            FpRealEncodingError::Unsupported => Self::Unsupported,
            FpRealEncodingError::EncodingGap => Self::EncodingGap,
        }
    }
}

type RealResult<T> = std::result::Result<T, FpRealError>;

impl From<UnknownOrigin> for FpRealError {
    fn from(origin: UnknownOrigin) -> Self {
        Self::Stopped(origin)
    }
}

impl Executor {
    /// The term arena can grow while rewriting or solving the Real side. Its
    /// admission snapshot in FpStop is not sufficient after those windows.
    pub(super) fn fp_real_checkpoint(
        &self,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
        phase: FpRealPhase,
    ) -> std::result::Result<(), UnknownOrigin> {
        observe(phase);
        stop.check()?;
        if self.term_memory_exceeded() {
            return Err(stop.refuse(UnknownOrigin::MemoryBudget));
        }
        Ok(())
    }

    pub(super) fn solve_fp_to_real(&mut self) -> Result<SolveResult> {
        self.solve_fp_to_real_observed(&|_| {})
    }

    fn solve_fp_to_real_observed(&mut self, observe: &impl Fn(FpRealPhase)) -> Result<SolveResult> {
        let stop = FpStop::from_executor(self);
        let proposed = self.run_fp_to_real(&stop, observe);
        // Outside every nested restoration and model-building window: clearing
        // a live flag cannot revive a stopped attempt or authorize its model.
        if let Err(origin) = self.fp_real_checkpoint(&stop, observe, FpRealPhase::Publication) {
            return Ok(self.fp_stopped(origin));
        }
        match proposed {
            Ok(result) => Ok(result),
            Err(FpRealError::Stopped(origin)) => Ok(self.fp_stopped(stop.refuse(origin))),
            Err(FpRealError::Executor(error)) => Err(error),
            Err(FpRealError::ModelDecode) => Ok(self.fp_model_decode_refusal()),
            Err(error) => {
                let origin = match error {
                    FpRealError::Unsupported => UnknownOrigin::UnsupportedFeature,
                    _ => UnknownOrigin::IncompleteSolverLane,
                };
                self.publish_unknown_from_origin(origin);
                Ok(SolveResult::Unknown)
            }
        }
    }

    fn admit_fp_real_sat(&mut self, encoding: &FpEncoding) -> SolveResult {
        if !encoding.congruence_incomplete {
            return SolveResult::Sat;
        }
        self.publish_unknown_from_origin(UnknownOrigin::IncompleteSolverLane);
        self.record_unknown_diagnostic(
            UnknownReason::Incomplete,
            "FP to_real congruence encoding omitted uninterpreted structure: its model \
             satisfies only a relaxation; UNSAT remains valid",
        );
        SolveResult::Unknown
    }

    fn store_unknown_or_unsat(
        &mut self,
        result: SatResult,
        tseitin: &ay_core::TseitinResult,
    ) -> Result<SolveResult> {
        self.solve_and_store_model_full(
            result, tseitin, None, None, None, None, None, None, None, None,
        )
    }
}
