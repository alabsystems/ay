// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! Branching optimization: exponential tightening + binary search.
//!
//! Satisfaction-path branching and shared types are in the parent module.

use ay_core::kani_compat::DetHashMap as HashMap;
use std::io::Write;

use crate::output::format_dzn_solution;
use crate::solver::{
    parse_ay_output, parse_get_value, parse_smt_int, run_ay, CheckSatResult, IncrementalSolver,
    SolverConfig, SolverError,
};
use crate::translate::{smt_int, TranslationResult};

use super::{
    backtrack_search, domain_is_enumerable, domain_lower_bound, domain_upper_bound, SearchOutcome,
    SearchPlanEntry,
};

/// Try to find a feasible solution via branching search (enumerable) or one-shot (fallback).
///
/// Returns `Some(values)` on SAT, `None` on UNSAT or UNKNOWN. Sets `*hit_unknown = true`
/// when ay returns UNKNOWN.
fn opt_try_solve(
    result: &TranslationResult,
    config: &SolverConfig,
    plan: &[SearchPlanEntry],
    query_vars: &[String],
    all_enumerable: bool,
    extra_assertions: &str,
    hit_unknown: &mut bool,
) -> Result<Option<HashMap<String, String>>, SolverError> {
    if all_enumerable && !plan.is_empty() {
        let decls = if extra_assertions.is_empty() {
            result.declarations.clone()
        } else {
            format!("{}{}", result.declarations, extra_assertions)
        };
        let mut solver = IncrementalSolver::new(config, &decls)?;
        match backtrack_search(&mut solver, plan, 0)? {
            SearchOutcome::Found => {
                let vars = query_vars.join(" ");
                Ok(Some(solver.get_value(&vars)?))
            }
            SearchOutcome::Unknown => {
                *hit_unknown = true;
                Ok(None)
            }
            SearchOutcome::NotFound => Ok(None),
        }
    } else {
        let mut script = result.declarations.clone();
        script.push_str(extra_assertions);
        script.push_str("(check-sat)\n");
        if !query_vars.is_empty() {
            let vars = query_vars.join(" ");
            script.push_str(&format!("(get-value ({vars}))\n"));
        }
        let output = run_ay(&script, config)?;
        let (status, lines) = parse_ay_output(&output)?;
        match status {
            CheckSatResult::Sat => Ok(Some(parse_get_value(&lines)?)),
            CheckSatResult::Unknown => {
                *hit_unknown = true;
                Ok(None)
            }
            CheckSatResult::Unsat => Ok(None),
        }
    }
}

pub(super) fn branching_optimization(
    result: &TranslationResult,
    config: &SolverConfig,
    plan: &[SearchPlanEntry],
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    let obj = result
        .objective
        .as_ref()
        .expect("called branching_optimization without objective");

    let mut query_vars: Vec<String> = plan.iter().map(|e| e.smt_var.clone()).collect();
    if !query_vars.contains(&obj.smt_expr) {
        query_vars.push(obj.smt_expr.clone());
    }

    let all_enumerable = plan.iter().all(|e| domain_is_enumerable(&e.domain));
    let mut solutions_found = 0;
    let mut hit_unknown = false;

    // Phase 1: Find first feasible solution (no objective bound).
    let first_found = opt_try_solve(
        result,
        config,
        plan,
        &query_vars,
        all_enumerable,
        "",
        &mut hit_unknown,
    )?;

    let first_obj_val = match first_found {
        Some(values) => {
            let dzn = format_dzn_solution(&values, &result.output_vars);
            write!(out, "{dzn}")?;
            writeln!(out, "----------")?;
            out.flush()?;
            solutions_found += 1;

            let val_str = values
                .get(&obj.smt_expr)
                .ok_or_else(|| SolverError::MissingObjective(obj.smt_expr.clone()))?;
            parse_smt_int(val_str)?
        }
        None => {
            if hit_unknown {
                writeln!(out, "=====UNKNOWN=====")?;
            } else {
                writeln!(out, "=====UNSATISFIABLE=====")?;
            }
            out.flush()?;
            return Ok(0);
        }
    };

    // Phase 2: Tighten the objective bound.
    //
    // Exponential tightening: start with step=1 from the current best,
    // double the step on each success. This keeps each probe close enough
    // to the current best for ay to solve quickly, while converging in
    // O(log(range)) steps. When a probe fails (UNSAT), binary search
    // within the last gap. When ay times out (UNKNOWN), stop.
    //
    // This outperforms pure binary search because SMT solvers struggle
    // with tight bounds far from the current best — they need to find a
    // model satisfying all constraints AND the tight bound simultaneously.
    let obj_domain = result.var_domains.get(&obj.smt_expr);
    let domain_bound = obj_domain.map(|d| {
        if obj.minimize {
            domain_lower_bound(d)
        } else {
            domain_upper_bound(d)
        }
    });

    let mut best_val = first_obj_val;
    let mut step: i64 = 1;

    'outer: loop {
        // Check global deadline before each probe.
        if config.deadline_expired() {
            break;
        }

        // Compute the probe target, clamping to domain bounds.
        let target = if obj.minimize {
            let t = best_val.saturating_sub(step);
            domain_bound.map_or(t, |lb| t.max(lb))
        } else {
            let t = best_val.saturating_add(step);
            domain_bound.map_or(t, |ub| t.min(ub))
        };

        // Check termination: target must be strictly better than best.
        let can_improve = if obj.minimize {
            target < best_val
        } else {
            target > best_val
        };
        if !can_improve {
            break;
        }

        let bound = if obj.minimize {
            format!("(assert (<= {} {}))\n", obj.smt_expr, smt_int(target))
        } else {
            format!("(assert (>= {} {}))\n", obj.smt_expr, smt_int(target))
        };

        let found = opt_try_solve(
            result,
            config,
            plan,
            &query_vars,
            all_enumerable,
            &bound,
            &mut hit_unknown,
        )?;

        match found {
            Some(values) => {
                let val_str = values
                    .get(&obj.smt_expr)
                    .ok_or_else(|| SolverError::MissingObjective(obj.smt_expr.clone()))?;
                let actual = parse_smt_int(val_str)?;

                let dzn = format_dzn_solution(&values, &result.output_vars);
                write!(out, "{dzn}")?;
                writeln!(out, "----------")?;
                out.flush()?;
                solutions_found += 1;

                best_val = actual;
                // Double the step on success — converge exponentially.
                step = step.saturating_mul(2);
            }
            None => {
                if hit_unknown {
                    // ay timed out. Stop optimizing.
                    break;
                }
                // UNSAT: no solution at target. Binary search in [target+1, best-1]
                // (minimize) or [best+1, target-1] (maximize) to find the exact bound.
                // Skip already-proven UNSAT target value.
                let (mut lo, mut hi) = if obj.minimize {
                    (target + 1, best_val - 1)
                } else {
                    (best_val + 1, target - 1)
                };
                while lo <= hi {
                    // Check deadline before each binary search probe.
                    if config.deadline_expired() {
                        break 'outer;
                    }

                    let mid = lo + (hi - lo) / 2;
                    let bound = if obj.minimize {
                        format!("(assert (<= {} {}))\n", obj.smt_expr, smt_int(mid))
                    } else {
                        format!("(assert (>= {} {}))\n", obj.smt_expr, smt_int(mid))
                    };

                    let found = opt_try_solve(
                        result,
                        config,
                        plan,
                        &query_vars,
                        all_enumerable,
                        &bound,
                        &mut hit_unknown,
                    )?;

                    match found {
                        Some(values) => {
                            let val_str = values.get(&obj.smt_expr).ok_or_else(|| {
                                SolverError::MissingObjective(obj.smt_expr.clone())
                            })?;
                            let actual = parse_smt_int(val_str)?;

                            let dzn = format_dzn_solution(&values, &result.output_vars);
                            write!(out, "{dzn}")?;
                            writeln!(out, "----------")?;
                            out.flush()?;
                            solutions_found += 1;

                            let _ = actual; // best_val not needed in binary search phase
                            if obj.minimize {
                                hi = actual - 1;
                            } else {
                                lo = actual + 1;
                            }
                        }
                        None => {
                            if hit_unknown {
                                break 'outer;
                            }
                            if obj.minimize {
                                lo = mid + 1;
                            } else {
                                hi = mid - 1;
                            }
                        }
                    }
                }
                // After binary search within the gap, optimality is proven
                // (all values in the gap are UNSAT). Done.
                break;
            }
        }
    }

    // Final output: claim optimality only if no UNKNOWN was encountered.
    if hit_unknown {
        // Cannot claim optimality when UNKNOWN was encountered.
        // Solutions already printed with "----------"; omit "==========" to
        // avoid claiming proven optimality.
        if solutions_found == 0 {
            writeln!(out, "=====UNKNOWN=====")?;
        }
    } else if solutions_found > 0 {
        writeln!(out, "==========")?;
    } else {
        writeln!(out, "=====UNSATISFIABLE=====")?;
    }
    out.flush()?;

    Ok(solutions_found)
}
