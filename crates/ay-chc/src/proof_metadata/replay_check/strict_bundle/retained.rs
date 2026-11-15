// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retained-v4 discharge carries live external-query authority into sealing.

use super::super::{retained_resources, verification_error, ChcObligationStrictCert};
use crate::pdr::ChcReplayObligation;
use crate::smt::executor_adapter::{
    check_plain_unsat_retained_native_with_progress, BoundRetainedProofBytes,
    RetainedReplayProgress,
};
use crate::ChcResult;

#[cfg(test)]
mod tests;

pub(in super::super) struct RetainedDischarge {
    pub(in super::super) cert: ChcObligationStrictCert,
    pub(in super::super) bound: BoundRetainedProofBytes,
    pub(in super::super) checker_command: String,
}

pub(in super::super) fn discharge_retained(
    obligation: &ChcReplayObligation,
    progress: &mut RetainedReplayProgress<'_>,
) -> ChcResult<RetainedDischarge> {
    // Each retained row is one obligation: one row's work envelope, with
    // its transient proof bytes settled when their owners drop.
    progress.begin_obligation().map_err(verification_error)?;
    progress.check().map_err(verification_error)?;
    let result = (|| {
        let checked = check_plain_unsat_retained_native_with_progress(&obligation.smtlib, progress)
            .map_err(verification_error)?;
        let bound = checked.encode(progress).map_err(verification_error)?;
        let bundle_sha256 = retained_resources::hash(bound.bundle_bytes(), &mut |work, bytes| {
            progress.charge(work, bytes)
        })?;
        let cert = ChcObligationStrictCert::new_retained(None, bundle_sha256, "verified");
        let command_bytes = obligation
            .name
            .len()
            .checked_add(256)
            .ok_or_else(|| verification_error("checked replay command size overflow"))?;
        retained_resources::admit(
            &mut |work, bytes| progress.charge(work, bytes),
            command_bytes,
            command_bytes,
        )?;
        let checker_command = format!(
            "{} --strict-retained-proof-bundle --expect unsat {}",
            super::super::CHC_IN_PROCESS_REPLAY_CHECKER_NAME,
            obligation.name,
        );
        Ok(RetainedDischarge {
            cert,
            bound,
            checker_command,
        })
    })();
    // All operation-local proof owners are gone before terminal admission.
    finish_discharge(progress, result)
}

fn finish_discharge<T>(
    progress: &mut RetainedReplayProgress<'_>,
    result: ChcResult<T>,
) -> ChcResult<T> {
    // Poll even after failure, but keep its actual cause. Native discharge
    // latches refusal on every error, so this terminal poll would otherwise
    // replace a source/proof rejection with a generic resource diagnostic.
    // Success still requires the unchanged original owner's final admission.
    let terminal = progress.check().map_err(verification_error);
    match result {
        Ok(discharge) => terminal.map(|()| discharge),
        Err(error) => Err(error),
    }
}
