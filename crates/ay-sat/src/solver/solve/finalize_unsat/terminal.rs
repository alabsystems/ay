// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The shared actual UNSAT finalization tail. Counted callers retain custody
//! through root-chain production, streaming support, cleanup and publication.
use super::*;
use crate::counted_storage::Result as AdmissionResult;
use crate::decision_trace::counted_decision::invalid;
use crate::solver::conflict_analysis_minimize_lrat::root;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, OriginalAdmissionError};

mod admission;
mod policy;
mod streaming;
#[cfg(test)]
mod tests;

use policy::Policy;

impl Solver {
    pub(in crate::solver) fn declare_counted_root_unsat(
        &mut self,
        conflict: Option<ClauseRef>,
        owner: &CountedAdmission,
        proof_progress: ProofProgress<'_>,
    ) -> Result<SatResult, SatUnknownReason> {
        // The original owner remains borrowed; this scope never owns the last
        // opaque observer/cancellation capture and never creates another grant.
        let mut scope = Scope {
            solver: self,
            owner,
            active: false,
            acquired: false,
            retained: false,
        };
        admission::prepare(scope.solver, owner, proof_progress)
            .map_err(counted_admission::reason)?;
        scope.active = true;
        scope.acquired = true;
        let p = root::Counted(owner);
        if let Some(reference) = conflict {
            scope
                .solver
                .record_lrat_level0_conflict_admitted(reference, &p)
                .map_err(counted_admission::reason)?;
        }
        admission::terminal(scope.solver, owner).map_err(counted_admission::reason)?;
        let result = scope
            .solver
            .finish_unsat_declaration_admitted(None, proof_progress, &p)
            .map_err(counted_admission::reason)?;
        scope.retire();
        owner.check().map_err(counted_admission::reason)?;
        scope.retained = true;
        Ok(result)
    }

    pub(in crate::solver) fn finish_unsat_declaration_admitted<P: Policy>(
        &mut self,
        backward: Option<BackwardProofResult>,
        progress: ProofProgress<'_>,
        p: &P,
    ) -> Result<SatResult, P::Error> {
        p.work(32)?;
        if let Err(error) = self.finalize_unsat_proof_with_progress(progress) {
            return p.proof_failure(self, error);
        }
        p.diagnostics(self)?;
        let mut certificate = match backward {
            Some(backward) => ProofCertificate::from_backward_reconstruction(backward),
            None => ProofCertificate::empty(),
        };
        if self.cold.retain_unsat_certificate {
            self.finalize_streaming_core_admitted(p)?;
            if let Some(core) = self.extract_streaming_core_admitted(p)? {
                certificate.set_streaming_support(core);
            }
        }
        if !self.poll_unsat_proof_progress(progress) {
            drop(certificate);
            return p.cancelled(self);
        }
        p.finish(self, SatResult::Unsat(certificate))
    }

    fn ordinary_unsat_diagnostics(&mut self) {
        self.tla_trace_step(CdclTraceState::Unsat, Some(CdclTraceAction::DeclareUnsat));
        let proof_steps = self
            .proof_manager
            .as_ref()
            .map_or(0, ProofManager::added_count);
        solver_log!(
            self,
            "UNSAT: {} conflicts, {} decisions, {} proof steps",
            self.num_conflicts,
            self.num_decisions,
            proof_steps
        );
        tracing::info!(
            num_conflicts = self.num_conflicts,
            num_decisions = self.num_decisions,
            proof_steps,
            "solve: unsat"
        );
        self.emit_diagnostic_unsat_summary();
    }
}

struct Scope<'a> {
    solver: &'a mut Solver,
    owner: &'a CountedAdmission,
    active: bool,
    acquired: bool,
    retained: bool,
}
impl Scope<'_> {
    fn retire(&mut self) {
        if self.active {
            for &vi in &self.solver.min.lrat_to_clear {
                self.solver.min.minimize_flags[vi] &= !LRAT_A;
            }
            self.solver.min.lrat_to_clear.clear();
            self.active = false;
        }
    }
}
impl Drop for Scope<'_> {
    fn drop(&mut self) {
        let unwinding = std::thread::panicking();
        if unwinding {
            self.owner.refuse(CountedAdmissionError::Original(
                OriginalAdmissionError::OperationPanicked,
            ));
        }
        self.retire();
        let healthy = self.owner.usage().is_ok_and(|u| u.refusal.is_none());
        if !self.retained || unwinding || !healthy {
            if self.acquired {
                if let Some(trace) = self.solver.cold.clause_trace.as_mut() {
                    trace.mark_proof_work_exhausted();
                }
            }
            if let Some(writer) = self.solver.cold.decision_trace.take() {
                writer.discard_without_flush();
            }
        }
    }
}
