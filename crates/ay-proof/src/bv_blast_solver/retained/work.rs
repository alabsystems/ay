// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive admission for measured replay work, not proof authority or a
//! whole-solver operation count. Callers must prepay the outer reservation.

use super::*;

/// Consumed by one capture/encode or decode/replay operation. Deliberately
/// neither Copy nor Clone: this value does not renew itself between phases.
pub(crate) struct WorkAllowance {
    limit: u64,
    deadline: Instant,
}

impl WorkAllowance {
    pub(crate) fn new(limit: u64, deadline: Instant) -> Self {
        Self { limit, deadline }
    }

    #[cfg(test)]
    pub(crate) fn work_limit(&self) -> u64 {
        self.limit
    }

    /// Inspect the original deadline without consuming or renewing the credit.
    pub(crate) fn deadline(&self) -> Instant {
        self.deadline
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct WorkUsage {
    pub(crate) producer_validation: u64,
    pub(crate) retained_prefix: u64,
    pub(crate) gates: u64,
    pub(crate) dag: u64,
    pub(crate) wire: u64,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Phase {
    Producer,
    Prefix,
    Gates,
    Dag,
    Wire,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum WorkError {
    #[error("retained work attempt already refused")]
    Refused,
    #[error("retained work deadline expired")]
    Deadline,
    #[error("retained phase reported {actual} work beyond its {limit} grant")]
    Exceeded { limit: u64, actual: u128 },
}

/// Success-only measured usage. Failed operations consume their outer prepaid
/// reservation and return no reusable remainder or partial proof.
/// The measured `work` is observed only by tests: production consumes the
/// whole prepaid allowance and never refunds or re-grants a remainder.
pub(crate) struct Metered<T> {
    pub(crate) value: T,
    #[cfg(test)]
    pub(crate) work: WorkUsage,
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum MeteredError {
    #[error(transparent)]
    Work(#[from] WorkError),
    #[error(transparent)]
    Proof(#[from] BvExprExportError),
    #[error(transparent)]
    Wire(#[from] wire::WireError),
}

pub(super) struct Ledger {
    remaining: u64,
    deadline: Instant,
    refused: bool,
    usage: WorkUsage,
}

impl Ledger {
    pub(super) fn new(allowance: WorkAllowance, deadline: Instant) -> Self {
        Self {
            remaining: allowance.limit,
            deadline: allowance.deadline.min(deadline),
            refused: false,
            usage: WorkUsage::default(),
        }
    }

    pub(super) fn deadline(&self) -> Instant {
        self.deadline
    }

    pub(super) fn check(&mut self) -> Result<(), WorkError> {
        if self.refused {
            return Err(WorkError::Refused);
        }
        if Instant::now() >= self.deadline {
            self.refused = true;
            return Err(WorkError::Deadline);
        }
        Ok(())
    }

    pub(super) fn phase<T>(
        &mut self,
        phase: Phase,
        ceiling: u64,
        operation: impl FnOnce(u64) -> Result<(T, u128), MeteredError>,
    ) -> Result<T, MeteredError> {
        self.check()?;
        let grant = ceiling.min(self.remaining);
        // A refusal or a caught panic cannot expose another allowance.
        self.refused = true;
        let (value, used) = operation(grant)?;
        if used > u128::from(grant) {
            return Err(WorkError::Exceeded {
                limit: grant,
                actual: used,
            }
            .into());
        }
        if Instant::now() >= self.deadline {
            return Err(WorkError::Deadline.into());
        }
        let used = used as u64; // Checked against a u64 grant above.
        self.remaining -= used;
        let counter = match phase {
            Phase::Producer => &mut self.usage.producer_validation,
            Phase::Prefix => &mut self.usage.retained_prefix,
            Phase::Gates => &mut self.usage.gates,
            Phase::Dag => &mut self.usage.dag,
            Phase::Wire => &mut self.usage.wire,
        };
        // All debits together fit the original u64 grant, hence so does this
        // phase's subset. Keep this explicit for future changes to the ledger.
        *counter = counter.checked_add(used).ok_or(WorkError::Exceeded {
            limit: u64::MAX,
            actual: u128::from(*counter) + u128::from(used),
        })?;
        self.refused = false;
        Ok(value)
    }

    pub(super) fn finish<T>(mut self, value: T) -> Result<Metered<T>, MeteredError> {
        self.check()?;
        Ok(Metered {
            value,
            #[cfg(test)]
            work: self.usage,
        })
    }
}

#[cfg(test)]
mod tests;
