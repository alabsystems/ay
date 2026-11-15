// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The certification deadline and the interrupt reach UNSAT proof assembly.
//!
//! `build_unsat_proof` runs after a search has refuted its query and before
//! certification decides whether the refutation may be published: in the
//! outer solve, and again inside every nested re-solve certification runs
//! (step (4) of the deferred-trust discharge, the checked isolated probes).
//! Its passes -- the empty-clause ladder with its SAT-trace replay, the
//! rewrite and Farkas passes, the authored repair cascade -- polled nothing
//! but the strict checks 301c34f88 reached, so an interrupt or deadline that
//! fired during assembly was first observed by `stop_declines_unsat_publication`
//! after the whole proof had been built, only to discard it. Measured on the
//! QF_AX `swap_t1_np_sf_ai_00009_007` row, where the deadline lands in step
//! (4)'s nested re-solve: `ay solve -t T` answered `unknown` 0.87-2.07 s after
//! T, 0.66 s of it in the trace replay alone.
//!
//! Every pass boundary, and the long loops inside the passes (the ladder's
//! rungs and its trace replay, the authored-cascade members, the congruence
//! and rewritten-assertion bridge candidates, the rewrite's derivation lanes),
//! now polls [`Executor::make_proof_assembly_should_stop`]: the interrupt, the
//! CERTIFICATION deadline, and the portfolio lane's memory share.
//!
//! Those are the conditions of the Certify node the assembly runs in
//! (GuardTree step S2, DR-39): `CancelOnly`, so it sees every cancel above it
//! (this executor's interrupt, the interrupts of the checks around it, the
//! lane's share, the process cancel) and keeps the certification envelope as
//! its own deadline, which the poll reads through a `DeadlinePoll` (DR-34),
//! never the clock at every callback. The node replaces the hand-written
//! "`make_should_stop` with the search wall swapped for the envelope".
//!
//! Not the search wall. A search lane narrows only `solve_deadline`, assembles
//! the refutation it found inside that slice, and restores the wall before
//! publication (`arrays_to_lia.rs` keeps an inner `solve_euf`/`solve_lia`
//! refutation; the DT lazy lane halves the wall around `solve_array_euf`). The
//! quantified backstop moves the wall the other way, and the per-call restore
//! unwinds it before `certify_unsat_for_publication` runs. In every flow that
//! reaches publication -- the command envelope, `set_deadline`, and the
//! `set_solve_controls` the native API and every derived certification
//! executor use -- the wall `stop_declines_unsat_publication` reads at
//! publication equals `certification_deadline`, which no search lane touches
//! (#certification-envelope-isolation). So a stop observed here is one
//! publication refuses anyway, and an expired slice the command may still
//! certify past never poisons the proof.
//!
//! A stop discards the half-built proof for the canonical fail-closed poison
//! (`install_uncertifiable_proof_poison`), together with the SAT-level LRAT
//! export of the discarded assembly. It never finishes, adopts or publishes a
//! partial proof.
//!
//! Every poll is also one OBSERVATION of the assembly count
//! (`proof/assembly_observations.rs`), charged to the owner. It adds no
//! budget of its own: the count stops an assembly only inside an allowance a
//! caller opened (step (4a)'s re-decision, #r30-4a-nested-assembly-count), at
//! an observation the query fixes, and that stop discards the proof the same
//! way.

use super::*;
use crate::executor::ProofDeclineMechanism;

impl Executor {
    /// The stop proof assembly observes: the cancels of its Certify node
    /// (this solve's interrupt, those of the checks around it, the portfolio
    /// lane's memory share, and the process-wide cancel: the run's owner
    /// ended it, and a stopped assembly is the fail-closed poison, never a
    /// proof) and its certification deadline, read live, never snapshotted.
    /// See the module docs for why the search wall is the wrong deadline
    /// here. The printer's complete bit-blast polls it at every callback, so
    /// the envelope is read through a `DeadlinePoll` (DR-34): a long poller
    /// reads a flag a timer raises, not the clock. Outside an assembly it
    /// builds a Certify node of its own, so a loop builds its stop once,
    /// before it, and polls that: one node per pass, never one per
    /// iteration. Every call charges one assembly observation and reports a
    /// stop once a caller's allowance of them is spent.
    pub(in crate::executor) fn make_proof_assembly_should_stop(&self) -> impl Fn() -> bool {
        let certify = self
            .assembly_certify
            .upgrade()
            .unwrap_or_else(|| self.proof_assembly_certify_node());
        let envelope =
            crate::executor::solve_deadline::DeadlinePoll::new(self.certification_deadline.clone());
        move || {
            assembly_observations::observe() || certify.cancelled().is_some() || envelope.expired()
        }
    }

    /// Whether [`Self::make_proof_assembly_should_stop`] reports a stop now:
    /// for a single check at a pass boundary, not for a loop's iterations.
    pub(in crate::executor) fn proof_assembly_stop_requested(&self) -> bool {
        self.make_proof_assembly_should_stop()()
    }

    /// At a pass boundary of `build_unsat_proof`: once a stop has fired,
    /// replace the unfinished proof by the fail-closed poison and tell the
    /// caller to return without running, adopting or installing anything else.
    pub(super) fn abandon_proof_assembly_on_stop(&mut self) -> bool {
        if !self.proof_assembly_stop_requested() {
            return false;
        }
        crate::executor::unsat_cert::probe_cert_reject(|| {
            let cause = if assembly_observations::allowance_spent() {
                "the caller's allowance of assembly observations is spent"
            } else {
                "interrupt or certification deadline fired"
            };
            format!(
                "proof assembly STOPPED: {cause} mid-assembly; the partial proof is \
                 discarded for the fail-closed poison"
            )
        });
        self.last_lrat_certificate = None;
        self.install_uncertifiable_proof_poison(ProofDeclineMechanism::ProofAssemblyStopped);
        true
    }
}

#[cfg(test)]
#[path = "stop_tests.rs"]
mod tests;
