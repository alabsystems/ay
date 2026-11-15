// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl RetainedProofCapture {
    /// Consume the pending owner AFTER its immutable first report was bound to
    /// the live external source by the caller. Internally narrow to the exact
    /// first-use inventory, then independently replay all retained evidence.
    /// This second check never captures replacement evidence or skips a lemma.
    ///
    /// The same original deadline and caller-owned cumulative callback cover
    /// allocation, mutation, replay, comparison and temporary-owner cleanup.
    /// Old owner reservations are never refunded. Success authenticates only
    /// the snapshot/context pairing, not the caller's external binding claim.
    pub fn finish_exact_with_resource_control(
        self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(RetainedProofBundle, BundleReCheck), ProofCheckError> {
        let deadline = self.deadline;
        // Move ALL input owners into the operation so early exits and success
        // drop first-check scratch before the enclosing final admission poll.
        control::run(deadline, progress, move |control| {
            let Self {
                mut snapshot,
                payloads,
                first,
                deadline,
            } = self;
            if !first.quality.is_complete() || first.assume_terms.is_empty() {
                return Err(control
                    .malformed("retained exact proof requires complete nonempty assumptions")?);
            }
            let inventory = control.ordered_unique(&first.assume_terms)?;
            let schema = control.copied_text(RETAINED_PROOF_BUNDLE_SCHEMA)?;
            let old_inventory = std::mem::replace(&mut snapshot.obligation_assertions, inventory);
            let old_schema = std::mem::replace(&mut snapshot.schema, schema);
            drop(old_inventory);
            drop(old_schema);
            drop(first);
            control.charge(0, 0)?;
            let envelope = retained::RetainedBundle::from_parts(
                snapshot,
                retained::RetainedField::Present(payloads),
            )
            .map_err(|_| ProofCheckError::ResourceLimit)?;
            let bundle = RetainedProofBundle {
                envelope,
                deadline,
                wire: transport_wire_limits(deadline),
            };
            let checked = bundle.replay(deadline, control)?;
            Ok((bundle, checked))
        })
    }
}
