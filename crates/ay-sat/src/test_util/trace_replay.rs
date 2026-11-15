// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only exact producer replay, distinct from repairing trace conversion.

#![cfg(test)]

use crate::ClauseTrace;
use ay_lrat_check::{checker::LratChecker, lrat_parser::LratStep, ConcludeResult};

/// Serialize each actual derived row, preserving its ID and recorded hints,
/// then use the standalone strict checker. Originals enter only at their
/// actual trace event: a later premise cannot justify an earlier derivation.
/// No canonical renumbering, extra hints or proof reconstruction is allowed.
pub(crate) fn strict_lrat_trace_replay(trace: &ClauseTrace, num_vars: usize) -> bool {
    let mut checker = LratChecker::new(num_vars);
    for entry in trace.entries().iter() {
        if entry.is_original {
            let clause: Vec<_> = entry
                .clause
                .iter()
                .map(|lit| {
                    ay_lrat_check::dimacs::Literal::try_from_dimacs(lit.to_dimacs()).unwrap()
                })
                .collect();
            if !checker.add_original(entry.id, &clause) {
                return false;
            }
            continue;
        }
        let mut line = format!("{} ", entry.id);
        for literal in entry.clause {
            line.push_str(&format!("{} ", literal.to_dimacs()));
        }
        line.push_str("0 ");
        for hint in entry.resolution_hints {
            line.push_str(&format!("{hint} "));
        }
        line.push_str("0\n");
        let steps = ay_lrat_check::lrat_parser::parse_text_lrat(&line).unwrap();
        let [LratStep::Add { id, clause, hints }] = steps.as_slice() else {
            panic!("exact row serialization must produce one addition");
        };
        if !checker.add_derived(*id, clause, hints) {
            return false;
        }
    }
    checker.conclude_unsat() == ConcludeResult::Verified
}
