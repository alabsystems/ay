// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use std::convert::Infallible;

pub(in crate::solver) trait Policy: root::Policy {
    fn diagnostics(&self, solver: &mut Solver) -> Result<(), Self::Error>;
    fn proof_failure(
        &self,
        solver: &mut Solver,
        error: UnsatProofFinalizationError,
    ) -> Result<SatResult, Self::Error>;
    fn cancelled(&self, solver: &mut Solver) -> Result<SatResult, Self::Error>;
    fn finish(&self, solver: &mut Solver, result: SatResult) -> Result<SatResult, Self::Error>;
}
impl Policy for root::Ordinary {
    fn diagnostics(&self, solver: &mut Solver) -> Result<(), Infallible> {
        solver.ordinary_unsat_diagnostics();
        Ok(())
    }
    fn proof_failure(
        &self,
        solver: &mut Solver,
        error: UnsatProofFinalizationError,
    ) -> Result<SatResult, Infallible> {
        Ok(
            if solver.cold.backward_proof_failure == Some(BackwardProofFailure::Cancelled) {
                solver.declare_unknown_with_reason(SatUnknownReason::Interrupted)
            } else {
                solver.declare_proof_finalization_unknown(error)
            },
        )
    }
    fn cancelled(&self, solver: &mut Solver) -> Result<SatResult, Infallible> {
        Ok(solver.declare_unknown_with_reason(solver.bounded_proof_unknown_reason()))
    }
    fn finish(&self, solver: &mut Solver, result: SatResult) -> Result<SatResult, Infallible> {
        Ok(solver.finish_counted_sat(result))
    }
}
impl Policy for root::Counted<'_> {
    fn diagnostics(&self, _: &mut Solver) -> AdmissionResult<()> {
        // Selected writers/subscribers were refused before scope transfer.
        self.0.admit(8, 0)
    }
    fn proof_failure(
        &self,
        _: &mut Solver,
        _: UnsatProofFinalizationError,
    ) -> AdmissionResult<SatResult> {
        Err(invalid(
            self.0,
            "counted terminal proof finalization failed",
        ))
    }
    fn cancelled(&self, _: &mut Solver) -> AdmissionResult<SatResult> {
        Err(invalid(
            self.0,
            "selected terminal progress callback refused",
        ))
    }
    fn finish(&self, _: &mut Solver, result: SatResult) -> AdmissionResult<SatResult> {
        self.0.check()?;
        Ok(result)
    }
}
