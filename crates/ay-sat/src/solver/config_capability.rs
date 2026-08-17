// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capability-ledger configuration accessors.

use super::*;

impl Solver {
    /// Install the startup capability ledger from the resolved variant plan.
    pub fn set_capability_ledger(&mut self, ledger: crate::auto::CapabilityLedger) {
        self.cold.capability_ledger = ledger;
    }

    /// The capability decisions taken while resolving this solver's startup plan.
    #[must_use]
    pub fn capability_ledger(&self) -> &crate::auto::CapabilityLedger {
        &self.cold.capability_ledger
    }
}
