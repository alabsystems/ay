// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cumulative constraint integration tests.

use super::*;

#[test]
fn test_cumulative_sat_sequential() {
    // Two tasks that can be scheduled sequentially on a single resource.
    let mut engine = CpSatEngine::new();
    let s0 = engine.new_int_var(Domain::new(0, 5), Some("s0"));
    let s1 = engine.new_int_var(Domain::new(0, 5), Some("s1"));
    let durs = const_vars(&mut engine, &[3, 2]);
    let dems = const_vars(&mut engine, &[1, 1]);

    engine.add_constraint(Constraint::Cumulative {
        starts: vec![s0, s1],
        durations: durs,
        demands: dems,
        capacity: 1,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let s0_val = assignment.iter().find(|(v, _)| *v == s0).unwrap().1;
            let s1_val = assignment.iter().find(|(v, _)| *v == s1).unwrap().1;
            let overlap = s0_val < s1_val + 2 && s1_val < s0_val + 3;
            assert!(
                !overlap,
                "tasks overlap: s0={s0_val} (dur 3), s1={s1_val} (dur 2)"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_cumulative_sat_parallel() {
    // Two tasks that can run in parallel because capacity is large enough.
    let mut engine = CpSatEngine::new();
    let s0 = engine.new_int_var(Domain::new(0, 5), Some("s0"));
    let s1 = engine.new_int_var(Domain::new(0, 5), Some("s1"));
    let durs = const_vars(&mut engine, &[3, 2]);
    let dems = const_vars(&mut engine, &[1, 1]);

    engine.add_constraint(Constraint::Cumulative {
        starts: vec![s0, s1],
        durations: durs,
        demands: dems,
        capacity: 2,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let s0_val = assignment.iter().find(|(v, _)| *v == s0).unwrap().1;
            let s1_val = assignment.iter().find(|(v, _)| *v == s1).unwrap().1;
            assert!((0..=5).contains(&s0_val), "s0 out of range: {s0_val}");
            assert!((0..=5).contains(&s1_val), "s1 out of range: {s1_val}");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_cumulative_unsat_overload() {
    // Three tasks that can't fit on a resource of capacity 2.
    // All 3 tasks have compulsory part at t=1 -> load=3 > 2.
    let mut engine = CpSatEngine::new();
    let s0 = engine.new_int_var(Domain::new(0, 1), Some("s0"));
    let s1 = engine.new_int_var(Domain::new(0, 1), Some("s1"));
    let s2 = engine.new_int_var(Domain::new(0, 1), Some("s2"));
    let durs = const_vars(&mut engine, &[3, 3, 3]);
    let dems = const_vars(&mut engine, &[1, 1, 1]);

    engine.add_constraint(Constraint::Cumulative {
        starts: vec![s0, s1, s2],
        durations: durs,
        demands: dems,
        capacity: 2,
    });

    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

#[test]
fn test_cumulative_extreme_endpoint_and_load_unsat() {
    let mut engine = CpSatEngine::new();
    let starts = const_vars(&mut engine, &[i64::MAX, i64::MAX]);
    let durations = const_vars(&mut engine, &[1, 1]);
    let demands = const_vars(&mut engine, &[i64::MAX, i64::MAX]);

    engine.add_constraint(Constraint::Cumulative {
        starts,
        durations,
        demands,
        capacity: i64::MAX,
    });

    assert!(
        matches!(engine.solve(), CpSolveResult::Unsat),
        "tasks overlapping beyond i64::MAX with total load 2*i64::MAX must be UNSAT"
    );
}

#[test]
fn test_cumulative_with_alldiff() {
    // Job-shop-like: 3 tasks on a single machine.
    let mut engine = CpSatEngine::new();
    let s0 = engine.new_int_var(Domain::new(0, 4), Some("s0"));
    let s1 = engine.new_int_var(Domain::new(0, 4), Some("s1"));
    let s2 = engine.new_int_var(Domain::new(0, 4), Some("s2"));
    let durs = const_vars(&mut engine, &[2, 2, 2]);
    let dems = const_vars(&mut engine, &[1, 1, 1]);

    engine.add_constraint(Constraint::Cumulative {
        starts: vec![s0, s1, s2],
        durations: durs,
        demands: dems,
        capacity: 1,
    });
    engine.add_constraint(Constraint::AllDifferent(vec![s0, s1, s2]));

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let s0_val = assignment.iter().find(|(v, _)| *v == s0).unwrap().1;
            let s1_val = assignment.iter().find(|(v, _)| *v == s1).unwrap().1;
            let s2_val = assignment.iter().find(|(v, _)| *v == s2).unwrap().1;

            let mut starts_durs = [(s0_val, 2i64), (s1_val, 2), (s2_val, 2)];
            starts_durs.sort_by_key(|&(s, _)| s);
            for pair in starts_durs.windows(2) {
                assert!(
                    pair[0].0 + pair[0].1 <= pair[1].0,
                    "tasks overlap: ({}, dur {}) and ({}, dur {})",
                    pair[0].0,
                    pair[0].1,
                    pair[1].0,
                    pair[1].1
                );
            }

            let start_vals = vec![s0_val, s1_val, s2_val];
            let mut sorted = start_vals.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(
                sorted.len(),
                3,
                "start times not all-different: {start_vals:?}"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_cumulative_with_linear() {
    // Two tasks with a makespan constraint.
    let mut engine = CpSatEngine::new();
    let s0 = engine.new_int_var(Domain::new(0, 3), Some("s0"));
    let s1 = engine.new_int_var(Domain::new(0, 4), Some("s1"));
    let durs = const_vars(&mut engine, &[3, 2]);
    let dems = const_vars(&mut engine, &[1, 1]);

    engine.add_constraint(Constraint::Cumulative {
        starts: vec![s0, s1],
        durations: durs,
        demands: dems,
        capacity: 1,
    });
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1],
        vars: vec![s0, s1],
        rhs: 5,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let s0_val = assignment.iter().find(|(v, _)| *v == s0).unwrap().1;
            let s1_val = assignment.iter().find(|(v, _)| *v == s1).unwrap().1;
            let overlap = s0_val < s1_val + 2 && s1_val < s0_val + 3;
            assert!(!overlap, "tasks overlap: s0={s0_val}, s1={s1_val}");
            assert!(
                s0_val + s1_val <= 5,
                "linear violated: {s0_val} + {s1_val} > 5"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}
