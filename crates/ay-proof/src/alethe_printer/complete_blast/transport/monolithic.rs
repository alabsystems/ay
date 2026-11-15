// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The monolithic refutation and its counted work envelope.
//!
//! A small circuit refutes its planned CNF in one CDCL search first; a large
//! one falls back to that search when the direct lane, the case split and the
//! sweep all declined (`Blaster::finish_planned`, d739a98f5), but not after a
//! sweep that refuted it and whose document only its size refused
//! (`size_refusal.rs`). Every other lane
//! runs inside an envelope of its own (`sweep.rs`); this one ran to
//! completion, and where the caller has no stop to poll (an observable
//! posture with neither an interrupt nor a deadline) nothing ended it.
//! Measured on the elaborated 64-bit affine identity of `bv_affine_source`
//! under `(set-option :check-proofs-strict true)` and no `:timeout`, read from
//! stdin: the wire-gap screen's ask spent the sweep's 120 s and was then
//! inside this search, on a 5,079-gate, 16,511-clause blast, until the run
//! was stopped at 1,500 s.
//!
//! [`MONOLITHIC_WORK`] bounds it in the solver's own counters, which the
//! search reads only to ask whether they are spent: inside the envelope the
//! refutation is the one the unbounded search finds. Where the envelope runs
//! out follows the search's trajectory, and that trajectory is fixed by the
//! CNF but for the first attempt's inprocessing, which wall-clock caps
//! schedule unless `--sat-deterministic-inproc` is set (`ay_sat`'s
//! `determinism.rs`): a circuit at the envelope's edge may refute on one run
//! and not on another. The refutation memo retains the refusal
//! (`resolution_dag_memo/within.rs`), so a repeated ask in the process
//! declines at once and agrees with the first, the support question with the
//! render. A refusal leaves the unproved step in place: it can cost a
//! document, never admit one. On the query above the first ask now declines
//! that blast 5.5 s after its sweep, and each later ask (twelve within the
//! 1,500 s) from the record, within the second of its sweep; the sweep's own
//! 120 s wall is still paid at every ask.

use super::super::Blaster;
use crate::resolution_dag_memo::prove_unsat_resolution_dag_memoized_within;
use ay_sat::{Literal, ResolutionDag, ResolutionDagError, ResolutionDagWork};

#[cfg(test)]
#[path = "monolithic_tests.rs"]
mod tests;

/// The monolithic refutation's envelope.
///
/// Measured 2026-10-07 at 6ccb67539 over every monolithic refutation the
/// complete blast completed in the ay-proof library tests, ay-dpll's `bv_*`
/// binaries and `group_proofs`, the 104 bit-vector conformance queries, and
/// external-codegen's 161 consumer-certificate queries under `--strict-proofs` with
/// no timeout: 178 refutations of up to 1,987 gates and 6,722 clauses, which
/// spent at most 2,484 conflicts and 28,085 decisions. Heavier ones are not
/// among them. The sweep takes external-codegen's `Sub_Lsl_Shift_I64 k=1` (8,399
/// clauses, `transport_tests.rs`) first in a document. Its first attempt
/// fails closed in LRAT authority after 4,817 conflicts and 32,481
/// decisions, and its retry refutes after 4,601 and 27,909 more; the
/// envelope, charged across both, is 10 times its 9,418 conflicts and 16
/// times its 60,390 decisions. `ay-dpll`'s library tests, which the 178 left
/// out, hold the heaviest measured, and it is printed:
/// `a_commuted_product_is_not_a_slice_identity` (an 8-bit product against
/// its commuted spelling, 862 gates, 2,112 clauses) refutes in 43,803
/// conflicts and 89,413 decisions from the CLI and in about 46,600 and
/// 91,600 in the library, and the CLI publishes that refutation's 54 MB
/// document as `carcara_surface=clean-dialect` (its `zero_extend` words are a
/// `cong` to `concat`, which pinned Carcara 1.1.0 refuses; LIMITATIONS.md).
/// The envelope is only 2.1 times its conflicts and 10.9 times its
/// decisions, and `monolithic_tests.rs` pins it inside. The elaborated 64-bit
/// affine identity above spent 1,000,000 conflicts (4,958,053 decisions,
/// 149,124,799 propagations) under a trial envelope of that size without
/// refuting.
pub(super) const MONOLITHIC_WORK: ResolutionDagWork = ResolutionDagWork {
    max_conflicts: 100_000,
    max_decisions: 1_000_000,
};

impl Blaster<'_, '_> {
    /// The monolithic CDCL refutation of `cnf` within [`MONOLITHIC_WORK`];
    /// `Err(true)` when the CNF is satisfiable, i.e. the lemma is false.
    ///
    /// A support question or render asked from inside a solve also polls the
    /// caller's stop (`super::super::CompleteBlastAsk`).
    pub(super) fn monolithic_refutation_planned(
        &self,
        variables: usize,
        cnf: &[Vec<Literal>],
    ) -> Result<ResolutionDag, bool> {
        self.monolithic_refutation_within(variables, cnf, MONOLITHIC_WORK)
    }

    /// [`Self::monolithic_refutation_planned`] within `work`.
    fn monolithic_refutation_within(
        &self,
        variables: usize,
        cnf: &[Vec<Literal>],
        work: ResolutionDagWork,
    ) -> Result<ResolutionDag, bool> {
        self.printer.complete_blast_progress().ok_or(false)?;
        let result = prove_unsat_resolution_dag_memoized_within(
            variables,
            cnf,
            work,
            Some(&|| self.printer.complete_blast_progress().is_none()),
        );
        self.printer.complete_blast_progress().ok_or(false)?;
        result.map_err(|error| {
            super::debug_note(|| {
                format!(
                    "the bit-blasting did not refute ({variables} gates, {} clauses): {error}",
                    cnf.len()
                )
            });
            matches!(error, ResolutionDagError::Satisfiable)
        })
    }
}
