// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::SatDiagnosticWriter;

impl SatDiagnosticWriter {
    /// Emit an incremental-scope push event.
    pub(crate) fn emit_scope_push(
        &self,
        scope_depth: usize,
        selector_var: u32,
        restored_clause_count: usize,
        num_conflicts: u64,
    ) {
        let event = serde_json::json!({
            "type": "scope_push",
            "scope_depth": scope_depth,
            "selector_var": selector_var,
            "restored_clause_count": restored_clause_count,
            "num_conflicts": num_conflicts,
        });
        self.write_event(&event);
    }

    /// Emit an incremental-scope pop event.
    pub(crate) fn emit_scope_pop(
        &self,
        scope_depth_before: usize,
        scope_depth_after: usize,
        selector_var: u32,
        retracted_empty_clause: bool,
        num_conflicts: u64,
    ) {
        let event = serde_json::json!({
            "type": "scope_pop",
            "scope_depth_before": scope_depth_before,
            "scope_depth_after": scope_depth_after,
            "selector_var": selector_var,
            "retracted_empty_clause": retracted_empty_clause,
            "num_conflicts": num_conflicts,
        });
        self.write_event(&event);
    }

    /// Emit an assumption batch event for one solve call.
    pub(crate) fn emit_assumption_batch(
        &self,
        count: usize,
        lits: &[i64],
        composed_with_scope: bool,
        num_conflicts: u64,
    ) {
        let event = serde_json::json!({
            "type": "assumption_batch",
            "count": count,
            "lits": lits,
            "composed_with_scope": composed_with_scope,
            "num_conflicts": num_conflicts,
        });
        self.write_event(&event);
    }

    /// Emit the terminal result for one assumption solve call.
    pub(crate) fn emit_assumption_result(
        &self,
        result: &str,
        core_size: Option<usize>,
        reason: Option<&str>,
        num_conflicts: u64,
    ) {
        let event = serde_json::json!({
            "type": "assumption_result",
            "result": result,
            "core_size": core_size,
            "reason": reason,
            "num_conflicts": num_conflicts,
        });
        self.write_event(&event);
    }
}
