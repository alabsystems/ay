// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource admission and streaming output for complete native v1 INPUT.

mod audit;
mod census;
mod meter;
mod plan;
mod stream;
#[cfg(test)]
mod tests;

use crate::api::{NativeReplayExportBudget, NativeReplayExportError, NativeReplayMetadata, Solver};
use meter::Meter;

impl Solver {
    /// Export the complete current native INPUT as compact diagnostic v1 JSON.
    ///
    /// Source/event/declaration/term payloads are inspected through borrows
    /// before materializing the bounded capture. All capture and serialization
    /// phases share the caller's cumulative budget. No solve is performed and
    /// no solver option, assertion, result, proof or replay authority changes.
    /// A refusal returns no partial problem or JSON prefix. As in the existing
    /// v1 artifact, assertions describe the current stack and the last recorded
    /// check event selects any replay assumptions; this does not issue or claim
    /// custody of a future solve. Solve evidence is deliberately absent.
    /// The current v1 reader's 128-level JSON nesting envelope also applies.
    ///
    /// Storage charges cover owned capture payloads, growing work/output
    /// collections and serialization temporaries, conservatively retaining
    /// charges when allocations are dropped. Work includes source bytes and
    /// visits, metadata comparison bounds, copying and serialization. They do
    /// not promise allocator bookkeeping, process RSS, preemption of caller
    /// callbacks or disposal of the caller's original input objects.
    ///
    /// # Errors
    ///
    /// Returns a structured refusal for exhausted limits, cancellation, invalid
    /// producer handles, allocation failure or source forms outside native v1.
    /// Needed UF/defined/datatype bindings and sort definitions absent from the
    /// native v1 history are refused rather than inferred or silently omitted.
    /// Text assertions whose dependencies are recorded remain representable.
    pub fn try_export_native_replay_input_json(
        &self,
        metadata: &NativeReplayMetadata,
        budget: &mut NativeReplayExportBudget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<String, NativeReplayExportError> {
        let mut meter = Meter { budget, progress };
        meter.poll()?;
        let admission = census::admit(self, metadata, &mut meter)?;
        admission.charge_headers(&mut meter)?;
        let plan = plan::build(self, metadata, admission.ordered_terms, &mut meter)?;
        audit::source(&plan, &mut meter)?;
        // Count the SAME borrowed v1 stream before allocating output. Capture
        // never constructs an owned artifact or a serde_json::Value tree.
        let result = stream::input(&plan, &mut meter)?;
        meter.poll()?;
        Ok(result)
    }
}
