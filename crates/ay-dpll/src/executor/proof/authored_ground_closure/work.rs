// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One shared allowance, with an explicit reason for a refused debit.

use super::*;

pub(super) const MAX_SHARED_WORK: usize = MAX_NODES * MAX_ROUNDS;

/// Not cloneable or refillable. A refused debit preserves the old remainder,
/// retires this meter, and authorizes only the existing final conflict check.
pub(super) struct SharedGroundWork {
    remaining: usize,
    refused: bool,
}

impl SharedGroundWork {
    pub(super) fn new(limit: usize) -> Self {
        Self {
            remaining: limit.min(MAX_SHARED_WORK),
            refused: false,
        }
    }

    pub(super) fn remaining(&self) -> usize {
        self.remaining
    }

    pub(super) fn refused(&self) -> bool {
        self.refused
    }

    #[track_caller]
    pub(super) fn spend(&mut self, units: usize) -> Option<()> {
        if self.refused {
            return None;
        }
        let Some(remaining) = self.remaining.checked_sub(units) else {
            self.refused = true;
            let site = std::panic::Location::caller();
            crate::executor::unsat_cert::probe_cert_reject(|| {
                format!(
                    "ground shared-work refusal remaining={} requested={units} site={}:{}",
                    self.remaining,
                    site.file(),
                    site.line()
                )
            });
            return None;
        };
        self.remaining = remaining;
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_work_keeps_failed_remainder_and_never_retries_or_refills() {
        let mut work = SharedGroundWork::new(3);
        assert_eq!(work.spend(2), Some(()));
        assert_eq!(work.remaining(), 1);
        assert_eq!(work.spend(2), None);
        assert_eq!(work.remaining(), 1);
        assert!(work.refused());
        assert_eq!(work.spend(0), None);
        assert_eq!(work.remaining(), 1);
    }

    #[test]
    fn shared_work_constructor_cannot_raise_the_existing_ceiling() {
        let mut work = SharedGroundWork::new(usize::MAX);
        assert_eq!(work.remaining(), 32_768);
        assert_eq!(work.spend(32_768), Some(()));
        assert_eq!(work.spend(1), None);
        assert_eq!(work.remaining(), 0);
    }
}
