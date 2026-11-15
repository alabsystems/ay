// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit unit-premise replay; structural evidence, not source authority.

use super::*;

impl ResolutionDag {
    /// Independently replay this DAG under the supplied ordered fixed units.
    ///
    /// The borrowed slice is scanned in its supplied order and is not retained
    /// or mutated. Units remain fixed during every RUP check. Duplicates count
    /// toward the clause, literal, byte and work
    /// limits; repeated equal units have the same logical effect as one.
    /// Opposite units are inconsistent, so any structurally admissible terminal
    /// refutation follows from those premises. No solver search is performed.
    ///
    /// This checks only `original_clauses AND fixed_unit_premises`. It does
    /// not authenticate either input against an authored query, temporary
    /// constraint, declaration context, scope, epoch or SMT variable map.
    /// Success must not be detached from the exact supplied units or promoted
    /// to an unconditional certificate. It does not produce a portable SMT/CHC
    /// proof or change the persistent SAT proof stream.
    ///
    /// The callback returns true to continue. Refusal is sticky within this
    /// call. The original absolute deadline and callback are checked again
    /// after replay scratch is destroyed, including after final callback work.
    /// Existing count, range, allocation and scratch checks remain in force.
    ///
    /// `max_bytes` additionally counts the borrowed unit slice's logical
    /// literal payload. The owner's excess capacity, allocator transients and
    /// other process memory still require a caller-owned memory envelope.
    ///
    /// Success reports the existing deterministic replay work, not callback
    /// count, source capture, proof production or SAT search. A caller continuing
    /// one finite grant must subtract successful usage once before its next
    /// phase. An error reports no usage and cannot authorize retrying with a
    /// renewed allowance. No additional retained-byte or initial-work bypass
    /// is exposed through this public method.
    pub fn validate_with_unit_premises_and_limits_and_cancellation_work(
        &self,
        fixed_unit_premises: &[Literal],
        limits: &ResolutionValidationLimits,
        keep_going: &mut dyn FnMut() -> bool,
    ) -> Result<u64, ResolutionValidationError> {
        let premise_bytes = checked_mul(
            fixed_unit_premises.len(),
            size_of::<Literal>(),
            ResolutionValidationResource::Bytes,
        )?;
        let mut stopped = false;
        let mut should_stop = || {
            if stopped {
                return true;
            }
            // Latch before caller code; refusal or unwinding cannot resume
            // this attempt. The borrowed callback never enters a proof writer.
            stopped = true;
            if keep_going() {
                stopped = false;
            }
            stopped
        };
        let work = self.validate_with_limits_interruptible(
            limits,
            fixed_unit_premises,
            premise_bytes,
            0,
            &mut should_stop,
        )?;
        // The private replay has returned and released all of its scratch.
        // Preserve ordinary replay errors by admitting only successful returns.
        if limits.deadline.is_some_and(|end| Instant::now() >= end) {
            return Err(ResolutionValidationError::DeadlineExceeded);
        }
        if should_stop() {
            return Err(ResolutionValidationError::Cancelled);
        }
        if limits.deadline.is_some_and(|end| Instant::now() >= end) {
            return Err(ResolutionValidationError::DeadlineExceeded);
        }
        Ok(work)
    }
}

#[cfg(test)]
mod tests;
