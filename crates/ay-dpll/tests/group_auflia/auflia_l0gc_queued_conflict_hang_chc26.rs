// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #triage-lra-const-eq liveness regression (CHC-COMP 2026 batch 3,
//! `llreve-bench/smt2/arrays/heap__findmax.array_000`).
//!
//! Batch 3 made LRA assert a CONSTANT equality (`x + 4 = x` cancels to
//! `4 = 0`) instead of skipping it, so a violated one is now a theory
//! conflict. That is correct — the skipped version accepted an inconsistent
//! assignment — but on this array-relational Houdini consecution query it
//! exposed a SAT-layer non-termination: a queued theory conflict clause that
//! a later root unit satisfied made `collect_level0_garbage` (run by
//! incremental inprocessing before the CDCL loop drains the queue) refuse the
//! delete, count it as progress, and loop forever without polling the
//! deadline (the query's own `:timeout 624` was ignored; the CHC v2 lane lost
//! 45 s and the instance timed out). Only the proof-shedding competition
//! posture reaches that state.
//!
//! The query is the exact executor-adapter text of the hung consecution
//! check minus its `:timeout` / `(get-model)` lines; z3 answers `unsat`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const QUERY: &str = include_str!("data/l0gc_queued_conflict_heap_findmax_v2.smt2");

fn verdicts(smt: &str, competition: bool) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    let mut out = Vec::new();
    for command in &commands {
        if let Some(line) = exec
            .execute_authored(command)
            .unwrap_or_else(|err| panic!("execution failed: {err}"))
        {
            let line = line.trim().to_owned();
            if matches!(line.as_str(), "sat" | "unsat" | "unknown") {
                out.push(line);
            }
        }
    }
    out
}

/// Competition posture: hung in level-0 GC before the fix; must terminate
/// with z3's verdict.
#[test]
#[timeout(60000)]
fn heap_findmax_v2_consecution_query_terminates_competition() {
    assert_eq!(verdicts(QUERY, true), vec!["unsat".to_owned()]);
}

/// Default proof-carrying posture: never hung; pins the same verdict.
#[test]
#[timeout(60000)]
fn heap_findmax_v2_consecution_query_default_posture() {
    assert_eq!(verdicts(QUERY, false), vec!["unsat".to_owned()]);
}
