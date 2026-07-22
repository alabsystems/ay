// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Read a JSONL file (one JSON object per line) into a Vec.
/// Used by both TLA trace and diagnostic trace tests.
pub(super) fn read_jsonl(path: &std::path::Path) -> Vec<serde_json::Value> {
    let contents = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    contents
        .lines()
        .map(|line| {
            serde_json::from_str(line)
                .unwrap_or_else(|e| panic!("invalid JSON in {}: {e}", path.display()))
        })
        .collect()
}

pub(super) fn read_tla_trace(path: &std::path::Path) -> Vec<serde_json::Value> {
    read_jsonl(path)
}

pub(super) fn read_diagnostic_trace(path: &std::path::Path) -> Vec<serde_json::Value> {
    read_jsonl(path)
}

pub(super) fn assert_single_unknown_result_summary_with_reason(
    events: &[serde_json::Value],
    expected_reason: &str,
) {
    let summaries: Vec<&serde_json::Value> = events
        .iter()
        .filter(|e| e["type"] == "result_summary" && e["result"] == "unknown")
        .collect();
    assert_eq!(
        summaries.len(),
        1,
        "expected exactly one UNKNOWN result_summary, got: {summaries:?}"
    );
    let summary = summaries[0];
    assert_eq!(
        summary["reason"], expected_reason,
        "expected reason '{expected_reason}' in diagnostic trace"
    );
    // The terminal event may be result_summary or assumption_result (when
    // the solve used the assumption API). Either way, find the last
    // result_summary to verify it's present and correct.
    let last_summary = events
        .iter()
        .rev()
        .find(|e| e["type"] == "result_summary")
        .expect("diagnostic trace should contain a result_summary event");
    assert_eq!(last_summary["result"], "unknown");
}

pub(super) fn assert_watch_invariant_for_all_active_clauses(solver: &Solver, stage: &str) {
    for clause_idx in solver.arena.active_indices() {
        let off = clause_idx;
        if solver.arena.is_empty_clause(off) || solver.arena.len_of(off) < 2 {
            continue;
        }
        let clause_ref = ClauseRef(clause_idx as u32);
        let lit0 = solver.arena.literal(clause_idx, 0);
        let lit1 = solver.arena.literal(clause_idx, 1);

        assert_ne!(
            lit0, lit1,
            "{stage}: clause {clause_idx} uses identical watch literals"
        );

        let has_w0 = (0..solver.watches.get_watches(lit0).len())
            .any(|i| solver.watches.get_watches(lit0).clause_ref(i) == clause_ref);
        let has_w1 = (0..solver.watches.get_watches(lit1).len())
            .any(|i| solver.watches.get_watches(lit1).clause_ref(i) == clause_ref);
        assert!(
            has_w0 && has_w1,
            "{stage}: clause {clause_idx} missing watch attachment for [{lit0:?}, {lit1:?}]"
        );
    }
}

pub(super) fn add_duplicate_and_gate_formula(solver: &mut Solver) {
    let a = Variable(0);
    let b = Variable(1);
    let g1 = Variable(2);
    let g2 = Variable(3);

    // g1 = AND(a, b)
    solver.add_clause(vec![
        Literal::negative(a),
        Literal::negative(b),
        Literal::positive(g1),
    ]);
    solver.add_clause(vec![Literal::positive(a), Literal::negative(g1)]);
    solver.add_clause(vec![Literal::positive(b), Literal::negative(g1)]);

    // g2 = AND(a, b)
    solver.add_clause(vec![
        Literal::negative(a),
        Literal::negative(b),
        Literal::positive(g2),
    ]);
    solver.add_clause(vec![Literal::positive(a), Literal::negative(g2)]);
    solver.add_clause(vec![Literal::positive(b), Literal::negative(g2)]);

    // Drive both gates true to force full gate reasoning.
    solver.add_clause(vec![Literal::positive(g1)]);
    solver.add_clause(vec![Literal::positive(g2)]);
}
