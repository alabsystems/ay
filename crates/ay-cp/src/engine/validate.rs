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
            if sum > *rhs {
                Err(format!("LinearLe violated: sum={sum} > rhs={rhs}"))
            } else {
                Ok(())
            }
        }

        Constraint::LinearEq { coeffs, vars, rhs } => {
            let sum = linear_sum(coeffs, vars, assignment);
            if sum != *rhs {
                Err(format!("LinearEq violated: sum={sum} != rhs={rhs}"))
            } else {
                Ok(())
            }
        }

        Constraint::LinearGe { coeffs, vars, rhs } => {
            let sum = linear_sum(coeffs, vars, assignment);
            if sum < *rhs {
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
            let mut events: Vec<(i64, i64)> = Vec::new(); // (time, demand_delta)
            for i in 0..n {
                let s = val(assignment, starts[i]);
                let d = val(assignment, durations[i]);
                let r = val(assignment, demands[i]);
                if d > 0 && r > 0 {
                    events.push((s, r));
                    events.push((s + d, -r));
                }
            }
            // Half-open intervals are active on [start, start + duration), so
            // tasks ending at time t must be removed before tasks starting at t.
            events.sort_by_key(|&(t, delta)| (t, delta > 0));
            let mut load: i64 = 0;
            for &(t, delta) in &events {
                load += delta;
                if load > *capacity {
                    return Err(format!(
                        "Cumulative violated at time {t}: load={load} > capacity={capacity}"
                    ));
                }
            }
            Ok(())
        }

        Constraint::Circuit(vars) => {
            let n = vars.len();
            if n == 0 {
                return Ok(());
            }
            let values: Vec<i64> = vars.iter().map(|v| val(assignment, *v)).collect();
            // Check all values are in range [0, n) or [1, n] depending on encoding.
            // ay-cp uses 0-indexed circuits: succ[i] ∈ [0, n-1].
            // But FlatZinc uses 1-indexed. Check both.
            let min_val = *values.iter().min().expect("invariant: non-empty circuit");
            let offset = min_val; // usually 0 or 1
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
                let next = (values[current] - offset) as usize;
                if next >= n {
                    return Err(format!(
                        "Circuit violated: successor {next} out of range for node {current}"
                    ));
                }
                current = next;
            }
            if !visited.iter().all(|&v| v) {
                return Err("Circuit violated: not all nodes visited".to_string());
            }
            Ok(())
        }

        Constraint::Inverse { x, y } => {
            // x[y[i]] = i for all i, and y[x[i]] = i for all i
            let n = x.len();
            let x_vals: Vec<i64> = x.iter().map(|v| val(assignment, *v)).collect();
            let y_vals: Vec<i64> = y.iter().map(|v| val(assignment, *v)).collect();
            let min_x = *x_vals.iter().min().unwrap_or(&0);
            let min_y = *y_vals.iter().min().unwrap_or(&0);
            for (i, &y_val) in y_vals.iter().enumerate().take(n) {
                let yi = (y_val - min_x) as usize;
                if yi >= n {
                    return Err(format!("Inverse violated: y[{i}]={y_val} out of range"));
                }
                if x_vals[yi] != (i as i64 + min_y) {
                    return Err(format!(
                        "Inverse violated: x[y[{i}]] = x[{}] = {} != {}",
                        yi,
                        x_vals[yi],
                        i as i64 + min_y
                    ));
                }
            }
            Ok(())
        }

        Constraint::BoolClause { pos, neg } => {
            // At least one pos var = 1 or one neg var = 0
            let satisfied = pos.iter().any(|v| val(assignment, *v) != 0)
                || neg.iter().any(|v| val(assignment, *v) == 0);
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
            if r != a.abs() {
                Err(format!("Abs violated: |{a}| = {} != result={r}", a.abs()))
            } else {
                Ok(())
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
            if vx - vy == *offset {
                Err(format!(
                    "PairwiseNeq violated: x={vx} - y={vy} = {} == offset={offset}",
                    vx - vy
                ))
            } else {
                Ok(())
            }
        }

        Constraint::LinearNotEqual { coeffs, vars, rhs } => {
            let sum = linear_sum(coeffs, vars, assignment);
            if sum == *rhs {
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
                    let x_overlap = xi < xj + dxj && xj < xi + dxi;
                    let y_overlap = yi < yj + dyj && yj < yi + dyi;
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
                    if !(si + durations[i] <= sj || sj + durations[j] <= si) {
                        return Err(format!(
                            "Disjunctive violated: task {i} [{si}, {}) overlaps task {j} [{sj}, {})",
                            si + durations[i],
                            sj + durations[j]
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
fn linear_sum(coeffs: &[i64], vars: &[IntVarId], assignment: &HashMap<IntVarId, i64>) -> i64 {
    coeffs
        .iter()
        .zip(vars.iter())
        .map(|(c, v)| c * val(assignment, *v))
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
        Constraint::Circuit(v) => v.clone(),
        Constraint::Inverse { x, y } => {
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
