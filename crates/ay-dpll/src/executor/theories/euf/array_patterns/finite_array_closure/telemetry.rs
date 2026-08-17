// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sticky incompleteness and exact-closure telemetry.

use super::*;

impl Executor {
    pub(super) fn record_finite_array_extensionality_report(
        &mut self,
        report: FiniteArrayExtensionalityReport,
    ) {
        for (key, value) in [
            (
                "smt.array.finite_ext.candidate_equalities",
                report.candidate_equalities,
            ),
            (
                "smt.array.finite_ext.candidate_index_points",
                report.candidate_index_points,
            ),
            (
                "smt.array.finite_ext.candidate_value_cells",
                report.candidate_value_cells,
            ),
            (
                "smt.array.finite_ext.candidate_selects",
                report.candidate_selects,
            ),
            (
                "smt.array.finite_ext.candidate_select_index_points",
                report.candidate_select_index_points,
            ),
            (
                "smt.array.finite_ext.candidate_select_value_cells",
                report.candidate_select_value_cells,
            ),
            (
                "smt.array.finite_ext.emitted_equalities",
                report.emitted_equalities,
            ),
            (
                "smt.array.finite_ext.emitted_index_points",
                report.emitted_index_points,
            ),
            (
                "smt.array.finite_ext.emitted_value_cells",
                report.emitted_value_cells,
            ),
            (
                "smt.array.finite_ext.emitted_selects",
                report.emitted_selects,
            ),
            (
                "smt.array.finite_ext.emitted_select_index_points",
                report.emitted_select_index_points,
            ),
            (
                "smt.array.finite_ext.emitted_select_value_cells",
                report.emitted_select_value_cells,
            ),
            (
                "smt.array.finite_ext.already_covered_equalities",
                report.already_covered_equalities,
            ),
            (
                "smt.array.finite_ext.already_covered_selects",
                report.already_covered_selects,
            ),
            (
                "smt.array.finite_ext.budget_deferred_equalities",
                report.budget_deferred_equalities,
            ),
            (
                "smt.array.finite_ext.budget_deferred_index_points",
                report.budget_deferred_index_points,
            ),
            (
                "smt.array.finite_ext.budget_deferred_value_cells",
                report.budget_deferred_value_cells,
            ),
            (
                "smt.array.finite_ext.budget_deferred_selects",
                report.budget_deferred_selects,
            ),
            (
                "smt.array.finite_ext.budget_deferred_select_index_points",
                report.budget_deferred_select_index_points,
            ),
            (
                "smt.array.finite_ext.budget_deferred_select_value_cells",
                report.budget_deferred_select_value_cells,
            ),
            (
                "smt.array.finite_ext.candidate_scan_truncated",
                report.candidate_scan_truncated,
            ),
        ] {
            let old = self.last_statistics.get_int(key).unwrap_or(0);
            self.last_statistics
                .set_int(key, old.saturating_add(value as u64));
        }
    }

    /// Record that a dedicated array route owns exact enumeration after its
    /// destructive preprocessing. Deferral is deliberately constant-time: a
    /// pre-substitution traversal would pay for the large raw store-flat DAG
    /// and could exhaust the query ledger before the owning route eliminates
    /// those aliases. Candidate and emission telemetry is recorded only by the
    /// later post-preprocess closure over the graph that is actually solved.
    pub(in crate::executor) fn record_finite_array_extensionality_route_deferral(&mut self) {
        let key = "smt.array.finite_ext.route_deferrals";
        let old = self.last_statistics.get_int(key).unwrap_or(0);
        self.last_statistics.set_int(key, old.saturating_add(1));
    }

    pub(super) fn mark_finite_array_scan_truncated(
        &mut self,
        report: &mut FiniteArrayExtensionalityReport,
    ) {
        // This report field is a closure-completeness flag, not a count of
        // nested callers that observed the same sticky query-level failure.
        // Once discovery truncates, every recursive scan declines too; record
        // that single cause once rather than inflating it per pending candidate.
        report.candidate_scan_truncated = 1;
        self.finite_array_expansion.candidate_scan_truncated = true;
    }
}
