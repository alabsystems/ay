// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keep the semantic BCP resume regression in ordinary tests. This control
//! uses only counted slice stops and verdicts.

use std::time::Duration;

use ay_core::resource::test_seams;
use ay_dpll::api::{Logic, Solver};

/// Far above either fixture's conflicts, so it bounds without deciding.
const RLIMIT: &str = "400000";
/// The forced size at which at least one round must stop on its own slice.
const SLICE_DIVISOR: u64 = 1024;
/// The historical BCP regression size and the forced slice-stop size.
const RESUME_DIVISORS: [u64; 2] = [64, SLICE_DIVISOR];
/// A hang detector, not a latency budget.
const BACKSTOP: Duration = Duration::from_secs(600);

struct SliceReset;

impl Drop for SliceReset {
    fn drop(&mut self) {
        test_seams::shrink_round_slices(1);
    }
}

fn fixture(name: &str) -> String {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/eager_persistent")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn solve(script: &str) -> (String, u64) {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver
        .try_set_option("rlimit", RLIMIT)
        .expect("an :rlimit is accepted");
    solver.set_timeout(Some(BACKSTOP));
    solver.parse_smtlib2(script).expect("fixture parses");
    let result = solver.check_sat();
    let verdict = format!("{:?}", result.result());
    let slice_stops = solver
        .statistics()
        .get_int("dpll.eager_persistent.slice_stops")
        .unwrap_or(0);
    (verdict, slice_stops)
}

#[test]
fn counted_search_reaches_verdict_at_the_bcp_regression_and_forced_slice_sizes() {
    test_seams::shrink_round_slices(1);
    let _reset = SliceReset;
    let mut forced_slice_stops = 0;
    for (name, verdict) in [
        ("sc-8.induction2.cvc.smt2", "Sat"),
        ("sc-5.base.cvc.smt2", "Unsat"),
    ] {
        let script = fixture(name);
        for divisor in RESUME_DIVISORS {
            test_seams::shrink_round_slices(divisor);
            let (result, slice_stops) = solve(&script);
            assert!(
                result.starts_with(verdict),
                "{name} with slices over {divisor}: {result}"
            );
            if divisor == SLICE_DIVISOR {
                forced_slice_stops += slice_stops;
            }
        }
    }
    assert!(
        forced_slice_stops > 0,
        "the forced size must stop a round on its own slice"
    );
}
