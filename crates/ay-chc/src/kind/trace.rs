// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl KindSolver {
    /// Build a TLA2 state snapshot aligned with `specs/kind_test.tla`.
    pub(super) fn kind_trace_snapshot(&self, k: usize, result: &str) -> serde_json::Value {
        serde_json::json!({
            "k": {"type": "int", "value": k as i64},
            "result": {"type": "string", "value": result},
            "phase": {"type": "string", "value": self.trace_phase.get()},
            "baseCaseChecked": {"type": "bool", "value": self.trace_base_case_checked.get()},
        })
    }

    /// Emit a single KIND trace step when trace output is enabled.
    pub(super) fn kind_trace_step_at(&self, k: usize, result: &str, action: Option<&str>) {
        if let Some(ref writer) = self.tla_trace {
            writer.write_step(self.kind_trace_snapshot(k, result), action);
        }
    }

    /// Flush the trace file.
    fn finish_kind_tla_trace(&self) {
        if let Some(ref writer) = self.tla_trace {
            let _ = writer.finish();
        }
    }

    /// Emit the terminal action for a solver result and flush the trace.
    pub(super) fn finish_with_result_trace(&self, k: usize, result: KindResult) -> KindResult {
        let (result_str, action) = match &result {
            KindResult::Safe(_) => ("Safe", "DeclareSafe"),
            KindResult::Unsafe(_) => ("Unsafe", "DeclareUnsafe"),
            KindResult::Unknown => ("Unknown", "DeclareUnknown"),
            KindResult::NotApplicable => ("NotApplicable", "DeclareNotApplicable"),
        };
        self.kind_trace_step_at(k, result_str, Some(action));
        self.finish_kind_tla_trace();
        result
    }
}
