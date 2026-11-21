// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The circuit, inverse and min/max encoders and the debug validator at the
//! ends of the i64 range (review of 2026-11-18, `cp-encoder-endpoints`).
//!
//! Node numbers, `value + 1` thresholds and decoded positions there leave
//! i64. Each case must give the right answer: never a panic (debug builds)
//! and never a wrapped value (release builds).

use super::*;
use crate::domain::Domain;
use crate::engine::CpSolveResult;

fn expect(engine: &mut CpSatEngine, sat: bool, what: &str) {
    match (sat, engine.solve()) {
        (true, CpSolveResult::Sat(_)) | (false, CpSolveResult::Unsat) => {}
        (expected, actual) => panic!("{what}: expected SAT={expected}, saw {actual:?}"),
    }
}

/// `result = min([arg])` with `result` fixed to `i64::MAX`: true exactly
/// when `arg` is `i64::MAX`. The encoder's first threshold was
/// `lb(result) + 1`: an overflow.
#[test]
fn test_minimum_at_integer_maximum() {
    for (argument, sat) in [(i64::MAX, true), (i64::MAX - 1, false)] {
        let mut engine = CpSatEngine::new();
        let result = engine.new_int_var(Domain::new(i64::MAX, i64::MAX), None);
        let arg = engine.new_int_var(Domain::new(argument, argument), None);
        engine.add_constraint(Constraint::Minimum {
            result,
            args: vec![arg],
        });
        expect(&mut engine, sat, &format!("min([{argument}]) = MAX"));
    }
}

/// `result = max([arg])` with `result` fixed to `i64::MIN`, the mirror case.
#[test]
fn test_maximum_at_integer_minimum() {
    for (argument, sat) in [(i64::MIN, true), (i64::MIN + 1, false)] {
        let mut engine = CpSatEngine::new();
        let result = engine.new_int_var(Domain::new(i64::MIN, i64::MIN), None);
        let arg = engine.new_int_var(Domain::new(argument, argument), None);
        engine.add_constraint(Constraint::Maximum {
            result,
            args: vec![arg],
        });
        expect(&mut engine, sat, &format!("max([{argument}]) = MIN"));
    }
}

/// Two successors over `base..=i64::MAX`: from `base = i64::MAX` there is
/// one value for two nodes (no circuit; the node numbering `base..base + 2`
/// is not representable), from `i64::MAX - 1` there are two. The encoder
/// panicked with "node range fits i64".
#[test]
fn test_circuit_needs_two_representable_distinct_successors() {
    for (base, sat) in [(i64::MAX, false), (i64::MAX - 1, true)] {
        let mut engine = CpSatEngine::new();
        let successors = (0..2)
            .map(|_| engine.new_int_var(Domain::new(base, i64::MAX), None))
            .collect();
        engine.add_constraint(Constraint::Circuit {
            succ: successors,
            base,
        });
        expect(&mut engine, sat, &format!("circuit from {base}"));
    }
}

/// See the circuit case.
#[test]
fn test_inverse_needs_two_representable_distinct_permutation_values() {
    for (base, sat) in [(i64::MAX, false), (i64::MAX - 1, true)] {
        let mut engine = CpSatEngine::new();
        let mut array = || -> Vec<IntVarId> {
            (0..2)
                .map(|_| engine.new_int_var(Domain::new(base, i64::MAX), None))
                .collect()
        };
        let x = array();
        let y = array();
        engine.add_constraint(Constraint::Inverse {
            x,
            y,
            base_x: base,
            base_y: base,
        });
        expect(&mut engine, sat, &format!("inverse from {base}"));
    }
}

/// Arrays of different lengths have no bijection between their index
/// sets: UNSAT. Debug builds panicked on an assertion; release builds
/// channelled the common prefix and answered SAT.
#[test]
fn test_inverse_of_different_lengths_is_unsatisfiable() {
    let mut engine = CpSatEngine::new();
    let x: Vec<IntVarId> = (0..2)
        .map(|_| engine.new_int_var(Domain::new(0, 1), None))
        .collect();
    let y: Vec<IntVarId> = (0..3)
        .map(|_| engine.new_int_var(Domain::new(0, 2), None))
        .collect();
    engine.add_constraint(Constraint::Inverse {
        x,
        y,
        base_x: 0,
        base_y: 0,
    });
    expect(&mut engine, false, "inverse of lengths 2 and 3");
}

const PERMS: [[i64; 3]; 6] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
];

/// Every pair of fixed permutations `x` (numbered from `x_base`) and `y`
/// (from `y_base`): SAT exactly when they are inverse, and then the
/// solution is the fixed values. With the bases at the ends of i64 the
/// debug validator subtracted the bases in i64 (an overflow), and before
/// 89d19c591 it rejected arrays numbered from different bases.
fn compare_inverse_pairs(x_base: i64, y_base: i64) {
    for x_perm in PERMS {
        for y_perm in PERMS {
            let inverse =
                (0..3).all(|i| y_perm[usize::try_from(x_perm[i]).expect("small")] == i as i64);
            let mut engine = CpSatEngine::new();
            let x = x_perm.map(|i| engine.new_int_var(Domain::singleton(x_base + i), None));
            let y = y_perm.map(|j| engine.new_int_var(Domain::singleton(y_base + j), None));
            engine.add_constraint(Constraint::Inverse {
                x: x.to_vec(),
                y: y.to_vec(),
                base_x: x_base,
                base_y: y_base,
            });
            let what = format!("bases {x_base}, {y_base}: x = {x_perm:?}, y = {y_perm:?}");
            match engine.solve() {
                CpSolveResult::Sat(assignment) => {
                    assert!(inverse, "{what}: SAT for arrays that are not inverse");
                    for (id, value) in x
                        .into_iter()
                        .zip(x_perm.map(|v| v + x_base))
                        .chain(y.into_iter().zip(y_perm.map(|v| v + y_base)))
                    {
                        assert!(assignment.contains(&(id, value)), "{what}: {assignment:?}");
                    }
                }
                CpSolveResult::Unsat => assert!(!inverse, "{what}: UNSAT for inverse arrays"),
                CpSolveResult::Unknown => panic!("{what}: unknown"),
            }
        }
    }
}

#[test]
fn test_inverse_numbering_distinct_bases() {
    compare_inverse_pairs(-3, 5);
}

#[test]
fn test_inverse_numbering_equal_bases() {
    compare_inverse_pairs(1, 1);
}

#[test]
fn test_inverse_numbering_upper_endpoint() {
    compare_inverse_pairs(i64::MAX - 2, -5);
}

#[test]
fn test_inverse_numbering_lower_endpoint() {
    compare_inverse_pairs(5, i64::MIN);
}

#[test]
fn test_inverse_numbering_both_endpoints() {
    compare_inverse_pairs(i64::MIN, i64::MAX - 2);
}

/// A circuit numbered against either end, every successor array of three
/// fixed values: SAT exactly for the two 3-cycles.
#[test]
fn test_circuit_numbering_at_both_endpoints() {
    for base in [i64::MIN, i64::MIN + 1, i64::MAX - 2] {
        for perm in PERMS {
            let cycle = perm == [1, 2, 0] || perm == [2, 0, 1];
            let mut engine = CpSatEngine::new();
            let succ: Vec<IntVarId> = perm
                .iter()
                .map(|&p| engine.new_int_var(Domain::singleton(base + p), None))
                .collect();
            engine.add_constraint(Constraint::Circuit { succ, base });
            expect(&mut engine, cycle, &format!("circuit {perm:?} from {base}"));
        }
    }
}

/// `|i64::MIN|` is not an i64: no result value can equal it, and the
/// largest, `i64::MAX`, is `|i64::MIN + 1|`.
#[test]
fn test_abs_at_integer_minimum() {
    for (argument, sat) in [(i64::MIN, false), (i64::MIN + 1, true)] {
        let mut engine = CpSatEngine::new();
        let result = engine.new_int_var(Domain::new(i64::MAX - 1, i64::MAX), None);
        let arg = engine.new_int_var(Domain::singleton(argument), None);
        engine.add_constraint(Constraint::Abs { result, arg });
        expect(&mut engine, sat, &format!("|{argument}|"));
    }
}

// The debug validator on values at the ends: it must report the violation,
// not overflow while decoding it.

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Circuit violated")]
fn test_validate_circuit_with_values_at_both_ends() {
    let mut engine = CpSatEngine::new();
    // One domain cannot hold both ends (its span is at most `i64::MAX`), two
    // can: the values below are `i64::MAX` and `i64::MIN`.
    let vars = vec![
        engine.new_int_var(Domain::new(i64::MAX - 1, i64::MAX), None),
        engine.new_int_var(Domain::new(i64::MIN, i64::MIN + 1), None),
    ];
    engine.debug_constraints.push(Constraint::Circuit {
        succ: vars.clone(),
        base: i64::MIN,
    });
    engine.debug_validate_assignment(&[(vars[0], i64::MAX), (vars[1], i64::MIN)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Inverse violated")]
fn test_validate_inverse_with_values_at_the_upper_end() {
    let mut engine = CpSatEngine::new();
    let x = vec![
        engine.new_int_var(Domain::new(i64::MAX - 1, i64::MAX), None),
        engine.new_int_var(Domain::new(i64::MAX - 1, i64::MAX), None),
    ];
    let y = vec![
        engine.new_int_var(Domain::new(0, 1), None),
        engine.new_int_var(Domain::new(0, 1), None),
    ];
    engine.debug_constraints.push(Constraint::Inverse {
        x: x.clone(),
        y: y.clone(),
        base_x: i64::MAX,
        base_y: 0,
    });
    engine.debug_validate_assignment(&[(x[0], i64::MAX), (x[1], i64::MAX), (y[0], 0), (y[1], 1)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Abs violated")]
fn test_validate_abs_of_integer_minimum() {
    let mut engine = CpSatEngine::new();
    let result = engine.new_int_var(Domain::new(i64::MAX - 1, i64::MAX), None);
    let arg = engine.new_int_var(Domain::new(i64::MIN, i64::MIN + 1), None);
    engine
        .debug_constraints
        .push(Constraint::Abs { result, arg });
    engine.debug_validate_assignment(&[(result, i64::MAX), (arg, i64::MIN)]);
}

// ------------------------------------------- explicit numbering (2026-11-19)

/// A circuit over the nodes 1..=3 whose successors can only be 2..=4 has
/// no solution (4 is no node, and three successors cannot share 2 and 3).
/// Read from the domains, the numbering was 2..=4, with a solution: the
/// meaning of the constraint depended on its domains. The wrapper that
/// keeps that rule still finds it.
#[test]
fn test_circuit_numbering_is_stated_not_read_from_domains() {
    let mut engine = CpSatEngine::new();
    let succ: Vec<IntVarId> = (0..3)
        .map(|_| engine.new_int_var(Domain::new(2, 4), None))
        .collect();
    engine.add_constraint(Constraint::Circuit {
        succ: succ.clone(),
        base: 1,
    });
    expect(&mut engine, false, "circuit over nodes 1..=3");

    let mut engine = CpSatEngine::new();
    let succ: Vec<IntVarId> = (0..3)
        .map(|_| engine.new_int_var(Domain::new(2, 4), None))
        .collect();
    let by_domains = engine.circuit_numbered_by_domains(succ);
    assert!(matches!(by_domains, Constraint::Circuit { base: 2, .. }));
    engine.add_constraint(by_domains);
    expect(&mut engine, true, "circuit over nodes 2..=4");
}

/// The same for inverse: `x` over 1..=2 and `y` over 1..=2 with every
/// value of `x` at least 2 (no position 1 of `y`): UNSAT when numbered from
/// 1; read from the domains, `x` was numbered from 2 and a solution found.
#[test]
fn test_inverse_numbering_is_stated_not_read_from_domains() {
    let build = |engine: &mut CpSatEngine| {
        let x: Vec<IntVarId> = (0..2)
            .map(|_| engine.new_int_var(Domain::new(2, 3), None))
            .collect();
        let y: Vec<IntVarId> = (0..2)
            .map(|_| engine.new_int_var(Domain::new(1, 2), None))
            .collect();
        (x, y)
    };
    let mut engine = CpSatEngine::new();
    let (x, y) = build(&mut engine);
    engine.add_constraint(Constraint::Inverse {
        x,
        y,
        base_x: 1,
        base_y: 1,
    });
    expect(&mut engine, false, "inverse numbered from 1");

    let mut engine = CpSatEngine::new();
    let (x, y) = build(&mut engine);
    let by_domains = engine.inverse_numbered_by_domains(x, y);
    assert!(matches!(
        by_domains,
        Constraint::Inverse {
            base_x: 2,
            base_y: 1,
            ..
        }
    ));
    engine.add_constraint(by_domains);
    expect(&mut engine, true, "inverse numbered from the domains");
}

/// A circuit of one node is that node succeeding itself. Before
/// 2026-11-19 a single successor had no constraint at all.
#[test]
fn test_single_node_circuit_succeeds_itself() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(3, 7), None);
    engine.add_constraint(Constraint::Circuit {
        succ: vec![x],
        base: 5,
    });
    match engine.solve() {
        CpSolveResult::Sat(assignment) => assert_eq!(assignment, vec![(x, 5)]),
        other => panic!("expected SAT, saw {other:?}"),
    }
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(3, 4), None);
    engine.add_constraint(Constraint::Circuit {
        succ: vec![x],
        base: 5,
    });
    expect(&mut engine, false, "single node 5 over 3..=4");
}
