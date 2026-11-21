// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-solve constraint validation (#6121).
//!
//! In debug builds, every SAT result is checked against the original CP
//! constraints. This catches encoding bugs, propagation errors, and
//! sign mistakes (like the #6119 count_eq d-sign bug) that produce
//! solutions violating the constraint model.

use std::collections::BTreeMap as HashMap;

use crate::propagator::Constraint;
use crate::variable::IntVarId;
use num_bigint::BigInt;

use super::CpSatEngine;

impl CpSatEngine {
    /// Validate that a SAT assignment satisfies all original constraints.
    ///
    /// Called via `debug_assert!` after every `CpSolveResult::Sat` return.
    /// Panics with a detailed error message if any constraint is violated.
    pub(super) fn debug_validate_assignment(&self, assignment: &[(IntVarId, i64)]) {
        let map: HashMap<IntVarId, i64> = assignment.iter().copied().collect();

        for (i, constraint) in self.debug_constraints.iter().enumerate() {
            if let Err(msg) = validate_constraint(constraint, &map) {
                let vars_str = format_constraint_vars(constraint, &map);
                panic!(
                    "BUG: CP-SAT post-solve validation failed (#6121)\n\
                     Constraint #{i}: {msg}\n\
                     Constraint: {constraint:?}\n\
                     Variable values: {vars_str}"
                );
            }
        }
    }
}

/// Check a single constraint against the assignment. Returns `Ok(())` if
/// satisfied, `Err(message)` if violated.
fn validate_constraint(
    constraint: &Constraint,
    assignment: &HashMap<IntVarId, i64>,
) -> Result<(), String> {
    match constraint {
        Constraint::AllDifferent(vars) => {
            let values: Vec<i64> = vars.iter().map(|v| val(assignment, *v)).collect();
            for i in 0..values.len() {
                for j in (i + 1)..values.len() {
                    if values[i] == values[j] {
                        return Err(format!(
                            "AllDifferent violated: var {:?}={} == var {:?}={}",
                            vars[i], values[i], vars[j], values[j]
                        ));
                    }
                }
            }
            Ok(())
        }

        Constraint::LinearLe { coeffs, vars, rhs } => {
            let sum = linear_sum(coeffs, vars, assignment);
            if sum > BigInt::from(*rhs) {
                Err(format!("LinearLe violated: sum={sum} > rhs={rhs}"))
            } else {
                Ok(())
            }
        }

        Constraint::LinearEq { coeffs, vars, rhs } => {
            let sum = linear_sum(coeffs, vars, assignment);
            if sum != BigInt::from(*rhs) {
                Err(format!("LinearEq violated: sum={sum} != rhs={rhs}"))
            } else {
                Ok(())
            }
        }

        Constraint::LinearGe { coeffs, vars, rhs } => {
            let sum = linear_sum(coeffs, vars, assignment);
            if sum < BigInt::from(*rhs) {
                Err(format!("LinearGe violated: sum={sum} < rhs={rhs}"))
            } else {
                Ok(())
            }
        }

        Constraint::Element {
            index,
            array,
            result,
        } => {
            let idx = val(assignment, *index);
            let res = val(assignment, *result);
            // Element constraint: result = array[index] (1-indexed in FlatZinc)
            // In ay-cp, the index variable's domain is already offset to be
            // 0-indexed into the array Vec.
            if idx < 0 || idx as usize >= array.len() {
                return Err(format!(
                    "Element index out of bounds: index={idx}, array.len={}",
                    array.len()
                ));
            }
            let arr_val = val(assignment, array[idx as usize]);
            if arr_val != res {
                Err(format!(
                    "Element violated: array[{idx}]={arr_val} != result={res}"
                ))
            } else {
                Ok(())
            }
        }

        Constraint::Table { vars, tuples } => {
            let values: Vec<i64> = vars.iter().map(|v| val(assignment, *v)).collect();
            if tuples.iter().any(|t| t == &values) {
                Ok(())
            } else {
                Err(format!(
                    "Table violated: ({values:?}) not in allowed tuples"
                ))
            }
        }

        Constraint::Cumulative {
            starts,
            durations,
            demands,
            capacity,
        } => {
            // Verify: at every time point, sum of demands of active tasks <= capacity.
            // Active tasks at time t: start[i] <= t < start[i] + duration[i].
            let n = starts.len();
            let mut events: Vec<(i128, i128)> = Vec::new(); // (time, demand_delta)
            for i in 0..n {
                let s = val(assignment, starts[i]);
                let d = val(assignment, durations[i]);
                let r = val(assignment, demands[i]);
                if d > 0 && r > 0 {
                    events.push((i128::from(s), i128::from(r)));
                    events.push((i128::from(s) + i128::from(d), -i128::from(r)));
                }
            }
            // Half-open intervals are active on [start, start + duration), so
            // tasks ending at time t must be removed before tasks starting at t.
            events.sort_by_key(|&(t, delta)| (t, delta > 0));
            let mut load = 0i128;
            for &(t, delta) in &events {
                load += delta;
                if load > i128::from(*capacity) {
                    return Err(format!(
                        "Cumulative violated at time {t}: load={load} > capacity={capacity}"
                    ));
                }
            }
            Ok(())
        }

        Constraint::Circuit { succ: vars, base } => {
            let n = vars.len();
            if n == 0 {
                return Ok(());
            }
            let values: Vec<i64> = vars.iter().map(|v| val(assignment, *v)).collect();
            // Nodes `base..base + n` (the constraint's own numbering; until
            // 2026-11-19 the smallest value of the solution was taken).
            let offset = *base;
            // Check: forms a single Hamiltonian cycle
            let mut visited = vec![false; n];
            let mut current = 0usize;
            for _ in 0..n {
                if visited[current] {
                    return Err(format!(
                        "Circuit violated: subcycle detected (revisited node {current})"
                    ));
                }
                visited[current] = true;
                // In i128: a wrong successor may lie anywhere in i64.
                let next = usize::try_from(i128::from(values[current]) - i128::from(offset))
                    .unwrap_or(usize::MAX);
                if next >= n {
                    return Err(format!(
                        "Circuit violated: successor {} out of range for node {current}",
                        values[current]
                    ));
                }
                current = next;
            }
            if !visited.iter().all(|&v| v) {
                return Err("Circuit violated: not all nodes visited".to_string());
            }
            Ok(())
        }

        Constraint::Inverse {
            x,
            y,
            base_x,
            base_y,
        } => {
            // x[y[i]] = i for all i, and y[x[i]] = i for all i
            let n = x.len();
            if y.len() != n {
                return Err(format!(
                    "Inverse violated: arrays of lengths {n} and {}",
                    y.len()
                ));
            }
            let x_vals: Vec<i64> = x.iter().map(|v| val(assignment, *v)).collect();
            let y_vals: Vec<i64> = y.iter().map(|v| val(assignment, *v)).collect();
            // Each array has its own node numbering (`encode_inverse`:
            // x[i] = j + base_x  <=>  y[j] = i + base_y). A value of y is
            // decoded with y's base and names a position of x, whose value
            // is compared in x's numbering. Until 2026-11-18 the two bases
            // were swapped here, which rejected every correct solution whose
            // arrays are numbered from different starts; until 2026-11-19
            // each base was the smallest value of the solution's array.
            let (base_x, base_y) = (*base_x, *base_y);
            // Every value of x in x's numbering (with y's check below, the
            // two arrays are inverse permutations).
            for (i, &x_val) in x_vals.iter().enumerate() {
                let j = i128::from(x_val) - i128::from(base_x);
                if usize::try_from(j).map_or(true, |j| j >= n) {
                    return Err(format!("Inverse violated: x[{i}]={x_val} out of range"));
                }
            }
            for (j, &y_val) in y_vals.iter().enumerate() {
                let i =
                    usize::try_from(i128::from(y_val) - i128::from(base_y)).unwrap_or(usize::MAX);
                if i >= n {
                    return Err(format!("Inverse violated: y[{j}]={y_val} out of range"));
                }
                let expected = i128::from(base_x) + j as i128;
                if i128::from(x_vals[i]) != expected {
                    return Err(format!(
                        "Inverse violated: x[y[{j}]] = x[{i}] = {} != {expected}",
                        x_vals[i]
                    ));
                }
            }
            Ok(())
        }

        Constraint::BoolClause { pos, neg } => {
            // The engine reads a Boolean as `[x >= 1]` (`encode_bool_clause`):
            // a positive literal holds when the value is at least 1, a
            // negative one when it is at most 0. Comparing with 0 instead
            // called a clause violated that a negative value satisfies.
            let satisfied = pos.iter().any(|v| val(assignment, *v) >= 1)
                || neg.iter().any(|v| val(assignment, *v) < 1);
            if satisfied {
                Ok(())
            } else {
                Err(
                    "BoolClause violated: no positive literal true and no negative literal false"
                        .to_string(),
                )
            }
        }

        Constraint::Abs { result, arg } => {
            let r = val(assignment, *result);
            let a = val(assignment, *arg);
            // `|i64::MIN|` is not an i64: compare in i128.
            let abs = i128::from(a).abs();
            if i128::from(r) != abs {
                Err(format!("Abs violated: |{a}| = {abs} != result={r}"))
            } else {
                Ok(())
            }
        }

        Constraint::Times { x, y, result } => {
            let (a, b, r) = (
                val(assignment, *x),
                val(assignment, *y),
                val(assignment, *result),
            );
            if i128::from(a) * i128::from(b) == i128::from(r) {
                Ok(())
            } else {
                Err(format!("Times violated: {a} * {b} != result={r}"))
            }
        }

        Constraint::Div { x, y, result } => {
            let (a, b, r) = (
                val(assignment, *x),
                val(assignment, *y),
                val(assignment, *result),
            );
            if b != 0 && i128::from(a) / i128::from(b) == i128::from(r) {
                Ok(())
            } else {
                Err(format!("Div violated: {a} div {b} != result={r}"))
            }
        }

        Constraint::Maximum { result, args } => {
            let r = val(assignment, *result);
            let max_val = args
                .iter()
                .map(|v| val(assignment, *v))
                .max()
                .unwrap_or(i64::MIN);
            if r != max_val {
                Err(format!(
                    "Maximum violated: max(args)={max_val} != result={r}"
                ))
            } else {
                Ok(())
            }
        }

        Constraint::Minimum { result, args } => {
            let r = val(assignment, *result);
            let min_val = args
                .iter()
                .map(|v| val(assignment, *v))
                .min()
                .unwrap_or(i64::MAX);
            if r != min_val {
                Err(format!(
                    "Minimum violated: min(args)={min_val} != result={r}"
                ))
            } else {
                Ok(())
            }
        }

        Constraint::PairwiseNeq { x, y, offset } => {
            let vx = val(assignment, *x);
            let vy = val(assignment, *y);
            let difference = i128::from(vx) - i128::from(vy);
            if difference == i128::from(*offset) {
                Err(format!(
                    "PairwiseNeq violated: x={vx} - y={vy} = {difference} == offset={offset}",
                ))
            } else {
                Ok(())
            }
        }

        Constraint::LinearNotEqual { coeffs, vars, rhs } => {
            let sum = linear_sum(coeffs, vars, assignment);
            if sum == BigInt::from(*rhs) {
                Err(format!("LinearNotEqual violated: sum={sum} == rhs={rhs}"))
            } else {
                Ok(())
            }
        }

        Constraint::Diffn { x, y, dx, dy } => {
            let n = x.len();
            for i in 0..n {
                let xi = val(assignment, x[i]);
                let yi = val(assignment, y[i]);
                let dxi = val(assignment, dx[i]);
                let dyi = val(assignment, dy[i]);
                for j in (i + 1)..n {
                    let xj = val(assignment, x[j]);
                    let yj = val(assignment, y[j]);
                    let dxj = val(assignment, dx[j]);
                    let dyj = val(assignment, dy[j]);
                    // Two rectangles overlap if they overlap on both axes
                    let x_overlap = i128::from(xi) < i128::from(xj) + i128::from(dxj)
                        && i128::from(xj) < i128::from(xi) + i128::from(dxi);
                    let y_overlap = i128::from(yi) < i128::from(yj) + i128::from(dyj)
                        && i128::from(yj) < i128::from(yi) + i128::from(dyi);
                    if x_overlap && y_overlap {
                        return Err(format!(
                            "Diffn violated: rect {i} ({xi},{yi},{dxi},{dyi}) \
                             overlaps rect {j} ({xj},{yj},{dxj},{dyj})"
                        ));
                    }
                }
            }
            Ok(())
        }

        Constraint::Disjunctive { starts, durations } => {
            let n = starts.len();
            for i in 0..n {
                let si = val(assignment, starts[i]);
                for j in (i + 1)..n {
                    let sj = val(assignment, starts[j]);
                    let end_i = i128::from(si) + i128::from(durations[i]);
                    let end_j = i128::from(sj) + i128::from(durations[j]);
                    if !(end_i <= i128::from(sj) || end_j <= i128::from(si)) {
                        return Err(format!(
                            "Disjunctive violated: task {i} [{si}, {end_i}) overlaps task {j} [{sj}, {end_j})"
                        ));
                    }
                }
            }
            Ok(())
        }
    }
}

/// Look up a variable's value in the assignment map.
fn val(assignment: &HashMap<IntVarId, i64>, var: IntVarId) -> i64 {
    *assignment
        .get(&var)
        .unwrap_or_else(|| panic!("BUG: variable {var:?} not in assignment"))
}

/// Compute a linear sum: sum(coeffs[i] * val(vars[i])).
fn linear_sum(coeffs: &[i64], vars: &[IntVarId], assignment: &HashMap<IntVarId, i64>) -> BigInt {
    coeffs
        .iter()
        .zip(vars.iter())
        .map(|(c, v)| BigInt::from(*c) * val(assignment, *v))
        .sum()
}

/// Format constraint variables and their values for error messages.
fn format_constraint_vars(constraint: &Constraint, assignment: &HashMap<IntVarId, i64>) -> String {
    let vars: Vec<IntVarId> = match constraint {
        Constraint::AllDifferent(v) => v.clone(),
        Constraint::LinearLe { vars, .. }
        | Constraint::LinearEq { vars, .. }
        | Constraint::LinearGe { vars, .. } => vars.clone(),
        Constraint::Element {
            index,
            array,
            result,
        } => {
            let mut v = vec![*index, *result];
            v.extend(array);
            v
        }
        Constraint::Table { vars, .. } => vars.clone(),
        Constraint::Cumulative {
            starts,
            durations,
            demands,
            ..
        } => {
            let mut v = starts.clone();
            v.extend(durations);
            v.extend(demands);
            v
        }
        Constraint::Circuit { succ, .. } => succ.clone(),
        Constraint::Inverse { x, y, .. } => {
            let mut v = x.clone();
            v.extend(y);
            v
        }
        Constraint::BoolClause { pos, neg } => {
            let mut v = pos.clone();
            v.extend(neg);
            v
        }
        Constraint::Abs { result, arg } => vec![*result, *arg],
        Constraint::Times { x, y, result } | Constraint::Div { x, y, result } => {
            vec![*x, *y, *result]
        }
        Constraint::Maximum { result, args } => {
            let mut v = vec![*result];
            v.extend(args);
            v
        }
        Constraint::Minimum { result, args } => {
            let mut v = vec![*result];
            v.extend(args);
            v
        }
        Constraint::PairwiseNeq { x, y, .. } => vec![*x, *y],
        Constraint::LinearNotEqual { vars, .. } => vars.clone(),
        Constraint::Disjunctive { starts, .. } => starts.clone(),
        Constraint::Diffn { x, y, dx, dy } => {
            let mut v = x.clone();
            v.extend(y);
            v.extend(dx);
            v.extend(dy);
            v
        }
    };

    vars.iter()
        .map(|v| {
            let value = assignment
                .get(v)
                .map_or("?".to_string(), ToString::to_string);
            format!("{v:?}={value}")
        })
        .collect::<Vec<_>>()
        .join(", ")
}
