// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owning, untrusted v6 snapshot paired with its mandatory retained inventory.
//!
//! This is an in-memory boundary, NOT a controlled JSON decoder or a checked
//! proof token. The caller must admit every source owner before construction.
//! The separate owning wire entry supplies that admission before assembly.
//! No serde implementation, mutable accessor, Deref or legacy conversion can
//! discard the inventory and turn this into a v5 snapshot. The actual schema
//! remains v6, so borrowing the snapshot cannot make a public v5 reader accept it.

use super::{PresenceError, RetainedField, RetainedStepPayload, RETAINED_SCHEMA};
use crate::bundle::SerializableProofBundle;

#[derive(Debug)]
pub(in crate::bundle) struct RetainedBundle {
    snapshot: SerializableProofBundle,
    payloads: Vec<RetainedStepPayload>,
}

impl RetainedBundle {
    /// Shape-only assembly from already-owned, separately admitted values.
    /// A present empty inventory is preserved; replay decides whether it is
    /// sufficient. No supplied schema or proof field is rewritten or cloned.
    pub(in crate::bundle) fn from_parts(
        snapshot: SerializableProofBundle,
        retained: RetainedField,
    ) -> Result<Self, PresenceError> {
        if snapshot.schema != RETAINED_SCHEMA {
            return Err(PresenceError::UnsupportedSchema);
        }
        match retained {
            RetainedField::Absent => Err(PresenceError::MissingRetainedField),
            RetainedField::Present(payloads) => Ok(Self { snapshot, payloads }),
        }
    }

    /// Shared reconstruction borrows both parts; neither carries authority.
    /// The immutable snapshot still bears v6 and cannot pass a v5 schema check.
    pub(in crate::bundle) fn parts(&self) -> (&SerializableProofBundle, &[RetainedStepPayload]) {
        (&self.snapshot, &self.payloads)
    }
}
