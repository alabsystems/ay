// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The counts a fresh re-decision's check-sat runs on in
//! `Executor::reconfirm_unsat_within`: its split-loop round trips
//! (#r30-reconfirm-slices-counted) and its proof assembly's observations
//! (#r30-4a-nested-assembly-count, `proof/assembly_observations.rs`).
//!
//! A spent round-trip count ends the nested check `Unknown` from
//! `DeterministicResourceBudget`. A spent assembly allowance ends the nested
//! proof assembly, which discards its unfinished proof for the fail-closed
//! poison; the check itself still answers `unsat`, and the poison's single
//! `trust` step is exactly the kind of rejection the re-decisions' structural
//! screen accepts as their entry condition. So the caller must decline such a
//! re-decision itself, by the count, before the screen ever sees it:
//! [`check_within_counts`] reports the spent allowance, and the caller never
//! screens a proof built past it.

use super::{Executor, FreshReconfirmationLimits};
use crate::api::proofs::TrustClauseDischargeControls;
use crate::executor::proof::assembly_observations;
use crate::executor_types::{Result, SolveResult};

/// The allowance of assembly observations a re-decision ran out of.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SpentAssemblyAllowance {
    /// The observations it was granted.
    pub(super) granted: u64,
    /// The observations it made: one past the allowance, or fewer when an
    /// enclosing allowance ran out first.
    pub(super) observed: u64,
}

impl std::fmt::Display for SpentAssemblyAllowance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "assembly allowance spent ({} observations of {})",
            self.observed, self.granted
        )
    }
}

/// Run `exec`'s check-sat on `limits`' counts, under `controls`' Certify
/// node when it has a round-trip count. The verdict, and the allowance of
/// assembly observations when the check spent it (anywhere: its own
/// assembly, or the assembly of a solve nested in it) or found an enclosing
/// one spent: either way the assembly stopped on a count, not on its proof.
pub(super) fn check_within_counts(
    exec: &mut Executor,
    limits: FreshReconfirmationLimits,
    controls: &TrustClauseDischargeControls,
) -> (Result<SolveResult>, Option<SpentAssemblyAllowance>) {
    let allowance = limits
        .max_assembly_observations
        .map(|granted| (granted, assembly_observations::enter_allowance(granted)));
    let verdict = match limits.max_round_trips {
        Some(round_trips) => controls.in_round_trips(round_trips, || exec.check_sat()),
        None => exec.check_sat(),
    };
    let spent = allowance.and_then(|(granted, scope)| {
        let observed = scope.spent();
        super::probe_cert_reject(|| {
            format!("re-decision assembly observations: {observed} of {granted}")
        });
        let stopped = observed > granted || assembly_observations::allowance_spent();
        stopped.then_some(SpentAssemblyAllowance { granted, observed })
    });
    (verdict, spent)
}
