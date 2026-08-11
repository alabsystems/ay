// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::domain::Domain;

#[cfg(debug_assertions)]
fn const_var(engine: &mut CpSatEngine, val: i64) -> IntVarId {
    engine.new_int_var(Domain::singleton(val), None)
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "LinearGe violated")]
fn test_validate_catches_linear_ge_violation() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(0, 10), None);
    let y = engine.new_int_var(Domain::new(0, 10), None);
    engine.debug_constraints.push(Constraint::LinearGe {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 8,
    });
    engine.debug_validate_assignment(&[(x, 3), (y, 4)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Element violated")]
fn test_validate_catches_element_violation() {
    let mut engine = CpSatEngine::new();
    let array0 = const_var(&mut engine, 10);
    let array1 = const_var(&mut engine, 20);
    let index = engine.new_int_var(Domain::singleton(1), None);
    let result = engine.new_int_var(Domain::new(0, 30), None);
    engine.debug_constraints.push(Constraint::Element {
        index,
        array: vec![array0, array1],
        result,
    });
    engine.debug_validate_assignment(&[(array0, 10), (array1, 20), (index, 1), (result, 10)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Table violated")]
fn test_validate_catches_table_violation() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 3), None);
    let y = engine.new_int_var(Domain::new(1, 3), None);
    engine.debug_constraints.push(Constraint::Table {
        vars: vec![x, y],
        tuples: vec![vec![1, 2], vec![2, 3]],
    });
    engine.debug_validate_assignment(&[(x, 3), (y, 1)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Cumulative violated")]
fn test_validate_catches_cumulative_violation() {
    let mut engine = CpSatEngine::new();
    let starts = vec![
        engine.new_int_var(Domain::new(0, 3), None),
        engine.new_int_var(Domain::new(0, 3), None),
    ];
    let duration0 = const_var(&mut engine, 3);
    let duration1 = const_var(&mut engine, 3);
    let demand0 = const_var(&mut engine, 2);
    let demand1 = const_var(&mut engine, 2);
    engine.debug_constraints.push(Constraint::Cumulative {
        starts: starts.clone(),
        durations: vec![duration0, duration1],
        demands: vec![demand0, demand1],
        capacity: 3,
    });
    engine.debug_validate_assignment(&[
        (starts[0], 0),
        (starts[1], 0),
        (duration0, 3),
        (duration1, 3),
        (demand0, 2),
        (demand1, 2),
    ]);
}

#[test]
#[cfg(debug_assertions)]
fn test_validate_accepts_cumulative_touching_intervals_6121() {
    let mut engine = CpSatEngine::new();
    let starts = [
        engine.new_int_var(Domain::new(0, 6), None),
        engine.new_int_var(Domain::new(0, 6), None),
    ];
    let duration0 = const_var(&mut engine, 3);
    let duration1 = const_var(&mut engine, 3);
    let demand0 = const_var(&mut engine, 2);
    let demand1 = const_var(&mut engine, 2);
    engine.debug_constraints.push(Constraint::Cumulative {
        starts: vec![starts[0], starts[1]],
        durations: vec![duration0, duration1],
        demands: vec![demand0, demand1],
        capacity: 3,
    });
    engine.debug_validate_assignment(&[
        (starts[0], 3),
        (starts[1], 0),
        (duration0, 3),
        (duration1, 3),
        (demand0, 2),
        (demand1, 2),
    ]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Cumulative violated")]
fn test_validate_cumulative_uses_wide_endpoint_and_load_arithmetic() {
    let mut engine = CpSatEngine::new();
    let starts = [
        const_var(&mut engine, i64::MAX),
        const_var(&mut engine, i64::MAX),
    ];
    let durations = [const_var(&mut engine, 1), const_var(&mut engine, 1)];
    let demands = [
        const_var(&mut engine, i64::MAX),
        const_var(&mut engine, i64::MAX),
    ];
    engine.debug_constraints.push(Constraint::Cumulative {
        starts: starts.to_vec(),
        durations: durations.to_vec(),
        demands: demands.to_vec(),
        capacity: i64::MAX,
    });
    engine.debug_validate_assignment(&[
        (starts[0], i64::MAX),
        (starts[1], i64::MAX),
        (durations[0], 1),
        (durations[1], 1),
        (demands[0], i64::MAX),
        (demands[1], i64::MAX),
    ]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Circuit violated: subcycle detected")]
fn test_validate_catches_circuit_violation() {
    let mut engine = CpSatEngine::new();
    let vars = vec![
        engine.new_int_var(Domain::new(0, 2), None),
        engine.new_int_var(Domain::new(0, 2), None),
        engine.new_int_var(Domain::new(0, 2), None),
    ];
    engine
        .debug_constraints
        .push(Constraint::Circuit(vars.clone()));
    engine.debug_validate_assignment(&[(vars[0], 1), (vars[1], 0), (vars[2], 2)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Inverse violated")]
fn test_validate_catches_inverse_violation() {
    let mut engine = CpSatEngine::new();
    let x = vec![
        engine.new_int_var(Domain::new(0, 2), None),
        engine.new_int_var(Domain::new(0, 2), None),
        engine.new_int_var(Domain::new(0, 2), None),
    ];
    let y = vec![
        engine.new_int_var(Domain::new(0, 2), None),
        engine.new_int_var(Domain::new(0, 2), None),
        engine.new_int_var(Domain::new(0, 2), None),
    ];
    engine.debug_constraints.push(Constraint::Inverse {
        x: x.clone(),
        y: y.clone(),
    });
    engine.debug_validate_assignment(&[
        (x[0], 1),
        (x[1], 2),
        (x[2], 0),
        (y[0], 1),
        (y[1], 0),
        (y[2], 2),
    ]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Abs violated")]
fn test_validate_catches_abs_violation() {
    let mut engine = CpSatEngine::new();
    let result = engine.new_int_var(Domain::new(0, 10), None);
    let arg = engine.new_int_var(Domain::new(-5, 5), None);
    engine
        .debug_constraints
        .push(Constraint::Abs { result, arg });
    engine.debug_validate_assignment(&[(result, 2), (arg, -3)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Maximum violated")]
fn test_validate_catches_maximum_violation() {
    let mut engine = CpSatEngine::new();
    let result = engine.new_int_var(Domain::new(0, 10), None);
    let args = vec![
        engine.new_int_var(Domain::new(0, 10), None),
        engine.new_int_var(Domain::new(0, 10), None),
    ];
    engine.debug_constraints.push(Constraint::Maximum {
        result,
        args: args.clone(),
    });
    engine.debug_validate_assignment(&[(result, 4), (args[0], 2), (args[1], 5)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Minimum violated")]
fn test_validate_catches_minimum_violation() {
    let mut engine = CpSatEngine::new();
    let result = engine.new_int_var(Domain::new(0, 10), None);
    let args = vec![
        engine.new_int_var(Domain::new(0, 10), None),
        engine.new_int_var(Domain::new(0, 10), None),
    ];
    engine.debug_constraints.push(Constraint::Minimum {
        result,
        args: args.clone(),
    });
    engine.debug_validate_assignment(&[(result, 3), (args[0], 4), (args[1], 5)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Diffn violated")]
fn test_validate_catches_diffn_violation() {
    let mut engine = CpSatEngine::new();
    let x = vec![
        engine.new_int_var(Domain::new(0, 5), None),
        engine.new_int_var(Domain::new(0, 5), None),
    ];
    let y = vec![
        engine.new_int_var(Domain::new(0, 5), None),
        engine.new_int_var(Domain::new(0, 5), None),
    ];
    let dx0 = const_var(&mut engine, 2);
    let dx1 = const_var(&mut engine, 2);
    let dy0 = const_var(&mut engine, 2);
    let dy1 = const_var(&mut engine, 2);
    engine.debug_constraints.push(Constraint::Diffn {
        x: x.clone(),
        y: y.clone(),
        dx: vec![dx0, dx1],
        dy: vec![dy0, dy1],
    });
    engine.debug_validate_assignment(&[
        (x[0], 0),
        (y[0], 0),
        (x[1], 1),
        (y[1], 1),
        (dx0, 2),
        (dx1, 2),
        (dy0, 2),
        (dy1, 2),
    ]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Diffn violated")]
fn test_validate_diffn_uses_wide_endpoint_arithmetic() {
    let mut engine = CpSatEngine::new();
    let x = [const_var(&mut engine, 1), const_var(&mut engine, 1)];
    let y = [const_var(&mut engine, 0), const_var(&mut engine, 0)];
    let dx = [const_var(&mut engine, i64::MAX), const_var(&mut engine, 1)];
    let dy = [const_var(&mut engine, 1), const_var(&mut engine, 1)];
    engine.debug_constraints.push(Constraint::Diffn {
        x: x.to_vec(),
        y: y.to_vec(),
        dx: dx.to_vec(),
        dy: dy.to_vec(),
    });
    engine.debug_validate_assignment(&[
        (x[0], 1),
        (x[1], 1),
        (y[0], 0),
        (y[1], 0),
        (dx[0], i64::MAX),
        (dx[1], 1),
        (dy[0], 1),
        (dy[1], 1),
    ]);
}
