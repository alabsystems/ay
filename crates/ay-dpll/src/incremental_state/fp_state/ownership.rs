// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Empty-shell ownership transfer and deferred push refusal.

use super::{IncrementalFpState, UnknownOrigin};

impl IncrementalFpState {
    /// Move the complete trial out, leaving no encoding/solver owner behind.
    /// The caller commits only a complete trial. Dropping or unwinding a trial
    /// leaves this same-scope shell ready for ordinary deferred rebuilding.
    /// Consume a pending namespace refusal before beginning an update.
    pub(crate) fn take_for_update(&mut self) -> Self {
        let mut shell = Self::new();
        shell.scope_depth = self.scope_depth;
        shell.pending_pushes = self.scope_depth;
        shell.disabled = self.disabled;
        // Do not lose a pending stop if an out-of-order caller drops its trial.
        shell.pending_namespace_refusal = self.pending_namespace_refusal;
        std::mem::replace(self, shell)
    }

    /// Deliver a push-time failure once, before admission or fallback gates.
    /// Internal teardown/pop cannot erase it; an explicit problem reset can.
    pub(crate) fn take_pending_namespace_refusal(&mut self) -> Option<UnknownOrigin> {
        self.pending_namespace_refusal.take()
    }

    fn refuse_push(&mut self) {
        self.reset_sat_encoding_for_rebuild();
        self.pending_namespace_refusal = Some(UnknownOrigin::DeterministicResourceBudget);
    }

    pub(super) fn push_checked(&mut self) {
        let Some(depth) = self.scope_depth.checked_add(1) else {
            if !self.disabled {
                self.refuse_push();
            }
            return;
        };
        self.scope_depth = depth;
        if self.disabled || self.pending_namespace_refusal.is_some() {
            // Disabled state allocates no SAT selectors. A pending failure
            // already tore the encoding down; preserve only frontend depth.
            self.pending_pushes = depth;
            return;
        }
        let selectors = if self.persistent_sat.is_some() {
            Some(1)
        } else {
            self.pending_pushes.checked_add(1)
        };
        if selectors.is_none_or(|count| self.checked_total_vars(0, count).is_err()) {
            self.refuse_push();
            return;
        }
        if let Some(sat) = self.persistent_sat.as_mut() {
            sat.push();
        } else {
            // checked above, without mutating the namespace on refusal.
            self.pending_pushes += 1;
        }
    }
}
