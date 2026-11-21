// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrow the established private-recovery ledger for a whole lane invocation.

use super::super::recovery_admission::{RecoveryAdmission, RecoveryRefusal, RecoveryScope};
use super::Executor;

/// The existing private model-recovery ceilings; shared across every function,
/// failed proposal, refinement round and final witness in this invocation.
const MAX_WORK: usize = 1_000_000;
const MAX_BYTES: usize = 64 * 1024 * 1024;

pub(in crate::executor) struct SymbolicRecoveryScope {
    _scope: RecoveryScope,
    admission: SymbolicAdmission,
}

#[derive(Clone)]
pub(in crate::executor) struct SymbolicAdmission(RecoveryAdmission);

impl std::fmt::Debug for SymbolicAdmission {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymbolicAdmission").finish_non_exhaustive()
    }
}

impl SymbolicRecoveryScope {
    pub(in crate::executor) fn enter(
        executor: &Executor,
        stop: Box<dyn Fn(usize, usize) -> bool + Send + Sync>,
    ) -> Option<Self> {
        let scope =
            RecoveryScope::enter_append_only_with_work_owner(executor, MAX_WORK, MAX_BYTES, stop)?;
        let admission = SymbolicAdmission(scope.admission());
        Some(Self {
            _scope: scope,
            admission,
        })
    }

    pub(in crate::executor) fn admission(&self) -> SymbolicAdmission {
        self.admission.clone()
    }
}

impl SymbolicAdmission {
    pub(in crate::executor) fn pay(&self, work: usize, bytes: usize) -> bool {
        self.0.pay(work, bytes)
    }

    /// Keep the original account through model publication and later reads.
    /// A foreign active transaction cannot be replaced by this capsule.
    pub(in crate::executor) fn pay_for(
        &self,
        executor: &Executor,
        work: usize,
        bytes: usize,
    ) -> bool {
        if !self.0.matches_append_only_source(executor) {
            self.0.refuse_with(RecoveryRefusal::Source);
            return false;
        }
        if RecoveryAdmission::current().is_some_and(|active| !self.0.shares_owner(&active)) {
            self.0.refuse_with(RecoveryRefusal::ForeignActiveOwner);
            return false;
        }
        if executor.poll_evaluation_stop().is_err() {
            self.0.refuse_with(RecoveryRefusal::ReadStop);
            return false;
        }
        if !self.0.pay(work, bytes) || executor.poll_evaluation_stop().is_err() {
            self.0.refuse_with(RecoveryRefusal::ReadStop);
            return false;
        }
        true
    }

    pub(in crate::executor) fn shares_owner(&self, other: &Self) -> bool {
        self.0.shares_owner(&other.0)
    }

    pub(in crate::executor) fn refuse(&self) {
        self.0.refuse();
    }

    pub(in crate::executor) fn refusal(&self) -> Option<RecoveryRefusal> {
        self.0.refusal()
    }

    #[cfg(test)]
    pub(in crate::executor) fn remaining(&self) -> (usize, usize) {
        self.0.remaining()
    }

    pub(in crate::executor) fn reserve<T>(&self, output: &mut Vec<T>, count: usize) -> Option<()> {
        let Some(bytes) = output
            .len()
            .checked_add(count)
            .and_then(|total| total.checked_add(output.capacity()))
            .and_then(|slots| slots.checked_mul(std::mem::size_of::<T>()))
        else {
            self.0.refuse();
            return None;
        };
        if !self.pay(count, bytes) || output.try_reserve_exact(count).is_err() {
            self.0.refuse();
            return None;
        }
        Some(())
    }
}
