// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The trace of a solve its original owner refused before any search.

use super::PdrSolver;
use crate::pdr::frame::PdrResult;

impl PdrSolver {
    /// Record an Unknown exit that an original owner refused before any
    /// search: the reason-bearing step and the `DeclareUnknown` terminal that
    /// every Unknown trace carries (#4697), then flush. Nothing else runs: no
    /// restatement, lemma export or other solver work follows a refusal.
    pub(in crate::pdr::solver) fn finish_refused_with_result_trace(
        &self,
        reason: &'static str,
    ) -> PdrResult {
        if let Some(ref writer) = self.tracing.tla_trace {
            let detail = serde_json::json!({
                "iterations": self.iterations,
                "frames": self.frames.len(),
            });
            self.pdr_trace_conservative_fail(reason, detail, None);
            let state = self.pdr_trace_snapshot("Unknown", None);
            let telemetry = self.build_telemetry_payload();
            writer.write_step_with_telemetry(state, Some("DeclareUnknown"), Some(telemetry));
        }
        self.finish_pdr_tla_trace();
        PdrResult::Unknown
    }
}
