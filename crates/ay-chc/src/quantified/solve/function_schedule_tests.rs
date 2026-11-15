// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn source(declarations: &str, sort: &str, function: &str) -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN) {declarations} {function}
         (declare-fun P ({sort}) Bool)
         (assert (forall ((x {sort})) (P x)))
         (assert (forall ((x {sort})) (=> (P x) false))) (check-sat)"
    ))
    .unwrap()
}

const FUNCTION: &str = "(declare-fun unused (Bool) (_ BitVec 136))";

#[test]
fn scalar_only_uf_search_keeps_the_wall_when_no_array_invariant_route_exists() {
    let source = source("", "(_ BitVec 8)", FUNCTION);
    let now = Instant::now();
    let deadline = now + Duration::from_secs(80);
    assert_eq!(
        source.counterexample_deadline(now, deadline),
        Some(deadline)
    );
}

#[test]
fn aggregate_uf_sources_reserve_time_for_full_original_safety_discharge() {
    let now = Instant::now();
    let deadline = now + Duration::from_secs(80);
    let array = source("", "(Array (_ BitVec 64) (_ BitVec 8))", FUNCTION);
    let record = source(
        "(declare-datatype Vec ((mkVec (data (Array (_ BitVec 64) (_ BitVec 8))))))",
        "Vec",
        FUNCTION,
    );
    for problem in [array, record] {
        assert_eq!(
            problem.counterexample_deadline(now, deadline),
            Some(now + Duration::from_secs(20)),
        );
    }
}

#[test]
fn function_free_scheduling_and_expired_deadlines_are_unchanged() {
    let now = Instant::now();
    let deadline = now + Duration::from_secs(80);
    for sort in ["(_ BitVec 8)", "(Array (_ BitVec 64) (_ BitVec 8))"] {
        let source = source("", sort, "");
        assert_eq!(
            source.counterexample_deadline(now, deadline),
            Some(now + Duration::from_secs(20)),
        );
        // Dispatch still rejects expired entry before calling this scheduler.
        assert_eq!(source.counterexample_deadline(now, now), Some(now));
    }
}
