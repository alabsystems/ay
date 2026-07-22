// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! VeriPB proof-stream emission for `PbCdclSolver`: per-step logging,
//! contradiction/UNSAT handling, and SAT/optimization proof conclusion.
//! Extracted from `cdcl.rs`; these remain methods on [`super::PbCdclSolver`].

use super::*;
use crate::cp_dense::ProvenResolveCapture;
use crate::proof::{format_constraint, ConstraintId, ProofError, ProofStep, VeriPbWriter};
use crate::types::PbObjective;

impl PbCdclSolver {
    pub(super) fn log_proof_step(&mut self, step: ProofStep) -> Option<ConstraintId> {
        if self.should_suppress_optimization_intermediate_proof_step(&step) {
            return None;
        }

        // Proof-tap route: everything that touches the proof text flows
        // through the ring in program order. Only the steps a tap-mode solve
        // can produce are encodable; any other step voids the proof (fail
        // closed) rather than silently skipping a line.
        if self.proof_tap.is_some() {
            return self.tap_log_step(step);
        }

        let result = self
            .proof_writer
            .as_mut()
            .map(|proof_writer| proof_writer.log_step(step));

        match result {
            Some(Ok(id)) => Some(id),
            Some(Err(error)) => {
                self.store_proof_error(error);
                None
            }
            None => None,
        }
    }

    fn tap_log_step(&mut self, step: ProofStep) -> Option<ConstraintId> {
        let tap = self.proof_tap.as_mut()?;
        let result = match step {
            ProofStep::Rup(text) => tap.log_rup_text(text).map(Some),
            ProofStep::Delete(pid) => tap.log_delete(pid).map(|()| Some(pid)),
            _ => Err(ProofError::TapUnsupportedStep(
                "only RUP and Delete steps are tap-encodable in this phase",
            )),
        };
        match result {
            Ok(id) => id,
            Err(error) => {
                self.store_proof_error(error);
                None
            }
        }
    }

    /// Opens a proof-tap capture frame for the conflict constraint. Returns
    /// `true` when the frame is open and micro-ops should be captured.
    /// Performs the mandatory per-conflict poison check; a missing conflict
    /// pid or a suppression window silently skips capture (the lemma then
    /// takes the RUP fallback / no logging, exactly like today).
    pub(super) fn tap_begin_conflict_frame(&mut self, conflict_cid: usize) -> bool {
        if self.proof_tap.is_none() || self.suppress_optimization_intermediate_proof_steps {
            return false;
        }
        let Some(conflict_pid) = self.proof_id_for_constraint(conflict_cid) else {
            return false;
        };
        let Some(tap) = self.proof_tap.as_mut() else {
            return false;
        };
        match tap.begin_frame(conflict_pid) {
            Ok(()) => true,
            Err(error) => {
                self.store_proof_error(error);
                false
            }
        }
    }

    /// Captures one accepted PROVEN round-to-one step. Returns `false` (and
    /// voids the tap) on transport failure so the caller stops capturing.
    pub(super) fn tap_capture_proven(
        &mut self,
        reason_pid: ConstraintId,
        capture: ProvenResolveCapture,
    ) -> bool {
        let Some(tap) = self.proof_tap.as_mut() else {
            return false;
        };
        match tap.proven_resolve(reason_pid, capture.c, capture.w, capture.weakened) {
            Ok(()) => true,
            Err(error) => {
                self.store_proof_error(error);
                false
            }
        }
    }

    /// Captures one accepted heuristic resolution step (see
    /// [`Self::tap_capture_proven`] for the error contract).
    pub(super) fn tap_capture_heuristic(
        &mut self,
        reason_pid: ConstraintId,
        capture: HeuristicResolveCapture,
    ) -> bool {
        let Some(tap) = self.proof_tap.as_mut() else {
            return false;
        };
        match tap.heuristic_resolve(
            reason_pid,
            capture.conflict_factor,
            capture.reason_factor,
            capture.div,
        ) {
            Ok(()) => true,
            Err(error) => {
                self.store_proof_error(error);
                false
            }
        }
    }

    /// Closes the open frame with the strengthening ops and stores the
    /// solver-allocated lemma id into `last_analysis_proof_id` (consumed by
    /// `add_learned_constraint`, exactly like the legacy path).
    pub(super) fn tap_final_frame_store(
        &mut self,
        gcd1: i128,
        weaken_ran: bool,
        weakened: Vec<PbLit>,
        gcd2: i128,
    ) {
        let Some(tap) = self.proof_tap.as_mut() else {
            return;
        };
        match tap.final_frame(gcd1, weaken_ran, weakened, gcd2) {
            Ok(lemma_pid) => self.last_analysis_proof_id = Some(lemma_pid),
            Err(error) => self.store_proof_error(error),
        }
    }

    /// Aborts any open capture frame (safe to call unconditionally; covers
    /// every early return out of conflict analysis).
    pub(super) fn tap_abort_frame_if_open(&mut self) {
        let Some(tap) = self.proof_tap.as_mut() else {
            return;
        };
        if let Err(error) = tap.abort_frame_if_open() {
            self.store_proof_error(error);
        }
    }

    /// Structured RUP fallback for a learned lemma under the tap (moves the
    /// constraint formatting off the solver thread). Returns the allocated id,
    /// or `None` when the constraint is not tap-encodable (matching the
    /// `format_pb_constraint` gate) or the tap failed.
    pub(super) fn tap_log_rup_constraint(
        &mut self,
        constraint: &PbConstraint,
    ) -> Option<ConstraintId> {
        use crate::types::PbRel;
        if constraint.rel != PbRel::Ge {
            return None;
        }
        let mut terms = Vec::with_capacity(constraint.terms.len());
        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            terms.push((*lit, term.coeff));
        }
        let tap = self.proof_tap.as_mut()?;
        match tap.log_rup(terms, constraint.rhs) {
            Ok(id) => Some(id),
            Err(error) => {
                self.store_proof_error(error);
                None
            }
        }
    }

    fn log_contradiction_proof_step(&mut self) -> Option<ConstraintId> {
        self.log_proof_step(ProofStep::Rup(format_constraint(&[], 1)))
    }

    fn should_suppress_optimization_intermediate_proof_step(&self, step: &ProofStep) -> bool {
        if !self.suppress_optimization_intermediate_proof_steps {
            return false;
        }

        // Whitelist deletions: a phase-1 lemma evicted by reduce_db during a
        // proof-on optimization re-solve must still be del'd. This fires only
        // on the LEGACY writer path today — the suppress flag is set solely
        // from proof_writer.is_some() (cdcl.rs, both opt loops) and a tap
        // solver fails closed out of the OPT loop before it can set the flag
        // (proof_tap.is_some() -> TapUnsupportedStep), so under the tap this
        // flag is always false and this branch is inert (FOLLOW-ON B item-3,
        // deferred to the tap-OPT phase). Suppressed-born constraints have no
        // pid (proof_id_for_constraint == None) and are filtered by the
        // caller's pid==None guard at search_maintenance.rs, so no dangling del
        // is possible.
        !matches!(step, ProofStep::Delete(_))
    }

    pub(super) fn handle_unsat_proof(&mut self, unsat_proof_mode: UnsatProofMode) {
        // Empty-lemma root refutation: dense analysis derived an empty
        // `>= degree>0` contradiction whose chain id is already a
        // checker-verified `false`. Conclude UNSAT directly on it instead of
        // emitting a redundant fresh `rup >= 1 ;`. take() also clears the flag
        // in DeriveOnly mode so it can never leak into a later Conclude.
        let root_refutation = self.root_refutation_proof_id.take();
        if unsat_proof_mode == UnsatProofMode::Conclude {
            if let Some(chain_id) = root_refutation {
                self.last_unsat_contradiction_proof_id = Some(chain_id);
                if let Some(mut tap) = self.proof_tap.take() {
                    match tap.conclude_unsat(chain_id) {
                        Ok(()) => self.proof_tap = Some(tap),
                        Err(error) => self.store_proof_error(error),
                    }
                    return;
                }
                let result = self
                    .proof_writer
                    .as_mut()
                    .map(|proof_writer| proof_writer.conclude_unsat(chain_id));
                if let Some(Err(error)) = result {
                    self.store_proof_error(error);
                    return;
                }
                self.flush_proof_writer();
                return;
            }
        }

        let Some(contradiction_id) = self.log_contradiction_proof_step() else {
            return;
        };
        self.last_unsat_contradiction_proof_id = Some(contradiction_id);

        if unsat_proof_mode == UnsatProofMode::DeriveOnly {
            return;
        }

        // Proof-tap route: the conclusion handshake BLOCKS until the
        // serializer has drained the ring, emitted the conclusion block, and
        // flushed — any buffered failure surfaces here, before the UNSAT
        // claim can commit.
        if let Some(mut tap) = self.proof_tap.take() {
            match tap.conclude_unsat(contradiction_id) {
                Ok(()) => self.proof_tap = Some(tap),
                Err(error) => self.store_proof_error(error),
            }
            return;
        }

        let result = self
            .proof_writer
            .as_mut()
            .map(|proof_writer| proof_writer.conclude_unsat(contradiction_id));

        if let Some(Err(error)) = result {
            self.store_proof_error(error);
            return;
        }

        self.flush_proof_writer();
    }

    /// Writes the VeriPB SAT conclusion with a complete assignment.
    ///
    /// VeriPB v3 requires `output NONE` followed by an explicit SAT conclusion.
    /// False assignment literals use `~xN`, matching OPB literal syntax rather
    /// than PB-COMP stdout witness syntax.
    pub(super) fn conclude_sat_proof(&mut self, assignment: &[bool]) {
        // Proof-tap route (same claim-commit handshake as UNSAT).
        if let Some(mut tap) = self.proof_tap.take() {
            match tap.conclude_sat(assignment) {
                Ok(()) => self.proof_tap = Some(tap),
                Err(error) => self.store_proof_error(error),
            }
            return;
        }

        let result = self
            .proof_writer
            .as_mut()
            .map(|proof_writer| proof_writer.conclude_sat(assignment));

        if let Some(Err(error)) = result {
            self.store_proof_error(error);
            return;
        }

        self.flush_proof_writer();
    }

    pub(super) fn conclude_opt_proof(&mut self, objective: &PbObjective, optimum: i128) {
        let contradiction_id =
            match self.try_log_objective_lower_bound_cut_proof(objective, optimum) {
                ObjectiveFloorCutOutcome::Derived(contradiction_id) => contradiction_id,
                ObjectiveFloorCutOutcome::EmissionFailed => {
                    // A step failed mid-chain: the error is already stored and the
                    // writer nulled (fail closed); attempting a conclusion now
                    // would be a no-op at best.
                    return;
                }
                ObjectiveFloorCutOutcome::Inexpressible => {
                    // Fail closed. The structural cutting-planes lower bound could not be
                    // built (the objective floor is not a positive combination of input
                    // rows — e.g. it needs a divide-by-k rounding cut or genuine search).
                    // Emitting `rup >= 1 ;` here would assert the empty clause is derivable
                    // by reverse unit propagation, but the learned clauses that actually
                    // justify it were SUPPRESSED during the optimization re-solves
                    // (suppress_optimization_intermediate_proof_steps), so VeriPB rejects
                    // it: "The constraint is not implied by reverse unit propagation (RUP)".
                    // Void this native proof and signal the caller (via conclude_proof's
                    // Err / opt_lower_bound_deferred) to route to the certified OPT-LIN
                    // fallback, which re-derives the bound from a real augmented-instance
                    // refutation whose RUP steps VeriPB accepts.
                    self.store_proof_error(ProofError::UnprovableOptimizationLowerBound);
                    return;
                }
            };

        // Hint both conclusion sides (contradiction row for the lower bound,
        // incumbent witness for the upper bound) so the proof also verifies in
        // unchecked-deletion mode, where the checker discounts `soli`-logged
        // solutions (VeriPB 3.0.2: "No solution has been logged in the proof
        // and no solution has been given in the conclusion").
        let witness = self.last_objective_bound_witness.take();
        let result = if let Some(proof_writer) = &mut self.proof_writer {
            match proof_writer.set_opt_bounds(optimum, optimum) {
                Ok(()) => Some(
                    proof_writer.conclude_opt_hinted(Some(contradiction_id), witness.as_deref()),
                ),
                Err(error) => Some(Err(error)),
            }
        } else {
            None
        };

        if let Some(Err(error)) = result {
            self.store_proof_error(error);
            return;
        }

        self.optimization_proof_pending = false;
        self.flush_proof_writer();
    }

    pub(super) fn conclude_opt_infeasible_proof(&mut self) {
        let result = self
            .proof_writer
            .as_mut()
            .map(VeriPbWriter::conclude_opt_infeasible);

        if let Some(Err(error)) = result {
            self.store_proof_error(error);
            return;
        }

        self.optimization_proof_pending = false;
        self.flush_proof_writer();
    }

    fn flush_proof_writer(&mut self) {
        let result = self.proof_writer.as_mut().map(VeriPbWriter::flush);

        if let Some(Err(error)) = result {
            self.store_proof_error(error);
        }
    }

    pub(super) fn store_proof_error(&mut self, error: ProofError) {
        if self.proof_error.is_none() {
            self.proof_error = Some(error);
        }
        self.proof_writer = None;
        // Dropping the tap closes the ring; the serializer drains and exits,
        // and — exactly like the writer-drop behaviour — later conflicts run
        // the unlogged dense path (same lemma algebra, search preserved).
        self.proof_tap = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PbInstance;

    fn empty_solver() -> PbCdclSolver {
        let instance = PbInstance {
            num_vars: 1,
            num_constraints: 0,
            constraints: Vec::new(),
            objective: None,
        };
        PbCdclSolver::new(&instance)
    }

    fn cid(raw: u64) -> ConstraintId {
        ConstraintId::new(raw).expect("nonzero id")
    }

    #[test]
    fn test_delete_whitelisted_through_suppression() {
        let mut solver = empty_solver();

        // Suppression OFF: nothing is suppressed, including Delete.
        solver.suppress_optimization_intermediate_proof_steps = false;
        assert!(!solver
            .should_suppress_optimization_intermediate_proof_step(&ProofStep::Delete(cid(5))));
        assert!(
            !solver.should_suppress_optimization_intermediate_proof_step(&ProofStep::Rup(
                String::from(">= 1 ;")
            ))
        );

        // Suppression ON: everything is suppressed EXCEPT Delete.
        solver.suppress_optimization_intermediate_proof_steps = true;
        assert!(!solver
            .should_suppress_optimization_intermediate_proof_step(&ProofStep::Delete(cid(5))));
        assert!(
            solver.should_suppress_optimization_intermediate_proof_step(&ProofStep::Rup(
                String::from(">= 1 ;")
            ))
        );
        assert!(
            solver.should_suppress_optimization_intermediate_proof_step(&ProofStep::Addition(
                cid(1),
                cid(2)
            ))
        );
        assert!(solver.should_suppress_optimization_intermediate_proof_step(
            &ProofStep::Polynomial(String::from("1 s ;"))
        ));
        assert!(solver
            .should_suppress_optimization_intermediate_proof_step(&ProofStep::Multiply(cid(1), 2)));
    }
}
