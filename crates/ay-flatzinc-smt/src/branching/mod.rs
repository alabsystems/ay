// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Branching search solver for FD-track compliance.
//
// Implements search-annotation-ordered solving using incremental ay solving.
// A persistent ay process handles push/pop for backtracking, with echo
// synchronization markers coordinating stdin/stdout. Fallback paths use
// one-shot invocations for non-enumerable domains.
//
// Optimization (exponential tightening + binary search) is in `optimize`.

mod optimize;

use ay_core::kani_compat::DetHashMap as HashMap;
use std::io::Write;

use crate::output::format_dzn_solution;
use crate::search::{SearchAnnotation, ValChoice, VarChoice};
use crate::solver::{
    parse_ay_output, parse_get_value, run_ay, CheckSatResult, IncrementalSolver, SolverConfig,
    SolverError,
};
use crate::translate::{smt_int, TranslationResult, VarDomain};

/// Resolve search variable names to their SMT-LIB equivalents.
fn resolve_search_vars(
    fzn_names: &[String],
    smt_var_names: &[String],
    var_domains: &HashMap<String, VarDomain>,
) -> Vec<String> {
    let mut result = Vec::new();
    for name in fzn_names {
        if var_domains.contains_key(name) {
            result.push(name.clone());
            continue;
        }
        let prefix = format!("{name}_");
        let mut array_vars: Vec<&String> = smt_var_names
            .iter()
            .filter(|v| v.starts_with(&prefix) && v[prefix.len()..].parse::<usize>().is_ok())
            .collect();
        array_vars.sort();
        if !array_vars.is_empty() {
            result.extend(array_vars.into_iter().cloned());
        }
    }
    result
}

/// Generate candidate values for a variable given its domain and value choice.
fn domain_candidates(domain: &VarDomain, val_choice: ValChoice) -> Vec<String> {
    match domain {
        VarDomain::Bool => match val_choice {
            ValChoice::IndomainMax | ValChoice::IndomainReverseSplit => {
                vec!["true".into(), "false".into()]
            }
            _ => vec!["false".into(), "true".into()],
        },
        VarDomain::IntRange(lo, hi) => {
            let mut vals: Vec<i64> = (*lo..=*hi).collect();
            order_int_values(&mut vals, val_choice);
            vals.iter().map(|v| smt_int(*v)).collect()
        }
        VarDomain::IntSet(values) => {
            let mut vals = values.clone();
            order_int_values(&mut vals, val_choice);
            vals.iter().map(|v| smt_int(*v)).collect()
        }
        VarDomain::IntUnbounded => {
            let mut vals: Vec<i64> = (-10..=10).collect();
            order_int_values(&mut vals, val_choice);
            vals.iter().map(|v| smt_int(*v)).collect()
        }
    }
}

/// Order integer values according to the value choice heuristic.
fn order_int_values(vals: &mut [i64], val_choice: ValChoice) {
    match val_choice {
        ValChoice::IndomainMin | ValChoice::Unknown => vals.sort_unstable(),
        ValChoice::IndomainMax => vals.sort_unstable_by(|a, b| b.cmp(a)),
        ValChoice::IndomainMedian => {
            vals.sort_unstable();
            if !vals.is_empty() {
                let mid = vals.len() / 2;
                let median = vals[mid];
                vals.sort_unstable_by_key(|v| (v - median).unsigned_abs());
            }
        }
        ValChoice::IndomainSplit => {
            vals.sort_unstable();
        }
        ValChoice::IndomainReverseSplit => {
            vals.sort_unstable_by(|a, b| b.cmp(a));
        }
        ValChoice::IndomainRandom => {}
    }
}

/// Outcome of a backtracking search over branching candidates.
///
/// Distinguishes between "definitely no solution" (all branches UNSAT)
/// and "couldn't determine" (at least one branch returned UNKNOWN).
/// Treating UNKNOWN as UNSAT is a soundness bug — see #327.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SearchOutcome {
    /// A satisfying assignment was found for all variables at this depth and below.
    Found,
    /// All branches were definitively unsatisfiable.
    NotFound,
    /// No solution was found, but at least one branch returned UNKNOWN,
    /// so unsatisfiability cannot be claimed.
    Unknown,
}

/// Solve using branching search with one-shot ay invocations.
pub fn solve_branching(
    result: &TranslationResult,
    config: &SolverConfig,
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    let search_plan = build_search_plan(result);

    if result.objective.is_some() {
        optimize::branching_optimization(result, config, &search_plan, out)
    } else {
        branching_satisfaction(result, config, &search_plan, out)
    }
}

/// A search plan entry: variable to branch on, with heuristic metadata.
struct SearchPlanEntry {
    smt_var: String,
    val_choice: ValChoice,
    domain: VarDomain,
}

/// Build a search plan from annotations, falling back to input order.
fn build_search_plan(result: &TranslationResult) -> Vec<SearchPlanEntry> {
    let mut plan = Vec::new();
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let default_domain = VarDomain::IntUnbounded;

    fn process_annotation(
        ann: &SearchAnnotation,
        result: &TranslationResult,
        plan: &mut Vec<SearchPlanEntry>,
        seen: &mut ay_core::kani_compat::DetHashSet<String>,
        default_domain: &VarDomain,
    ) {
        match ann {
            SearchAnnotation::IntSearch {
                vars,
                var_choice,
                val_choice,
                ..
            }
            | SearchAnnotation::BoolSearch {
                vars,
                var_choice,
                val_choice,
                ..
            } => {
                let group_start = plan.len();
                let smt_vars =
                    resolve_search_vars(vars, &result.smt_var_names, &result.var_domains);
                for v in smt_vars {
                    if seen.insert(v.clone()) {
                        let domain = result
                            .var_domains
                            .get(&v)
                            .cloned()
                            .unwrap_or_else(|| default_domain.clone());
                        plan.push(SearchPlanEntry {
                            smt_var: v,
                            val_choice: *val_choice,
                            domain,
                        });
                    }
                }
                apply_var_choice_order(&mut plan[group_start..], *var_choice);
            }
            SearchAnnotation::SeqSearch(inner) => {
                for a in inner {
                    process_annotation(a, result, plan, seen, default_domain);
                }
            }
        }
    }

    for ann in &result.search_annotations {
        process_annotation(ann, result, &mut plan, &mut seen, &default_domain);
    }

    for v in &result.smt_var_names {
        if seen.insert(v.clone()) {
            let domain = result
                .var_domains
                .get(v)
                .cloned()
                .unwrap_or_else(|| default_domain.clone());
            plan.push(SearchPlanEntry {
                smt_var: v.clone(),
                val_choice: ValChoice::IndomainMin,
                domain,
            });
        }
    }

    plan
}

/// Sort plan entries within a group according to the variable choice heuristic.
fn apply_var_choice_order(group: &mut [SearchPlanEntry], var_choice: VarChoice) {
    match var_choice {
        VarChoice::InputOrder | VarChoice::Unknown => {}
        VarChoice::FirstFail | VarChoice::MostConstrained | VarChoice::DomWDeg => {
            group.sort_by_key(|e| domain_size(&e.domain));
        }
        VarChoice::AntiFirstFail => {
            group.sort_by_key(|b| std::cmp::Reverse(domain_size(&b.domain)));
        }
        VarChoice::Smallest => {
            group.sort_by_key(|e| domain_lower_bound(&e.domain));
        }
        VarChoice::Largest => {
            group.sort_by_key(|b| std::cmp::Reverse(domain_upper_bound(&b.domain)));
        }
    }
}

fn domain_size(domain: &VarDomain) -> i64 {
    match domain {
        VarDomain::Bool => 2,
        VarDomain::IntRange(lo, hi) => hi.saturating_sub(*lo).saturating_add(1),
        VarDomain::IntSet(vals) => vals.len() as i64,
        VarDomain::IntUnbounded => i64::MAX,
    }
}

fn domain_lower_bound(domain: &VarDomain) -> i64 {
    match domain {
        VarDomain::Bool => 0,
        VarDomain::IntRange(lo, _) => *lo,
        VarDomain::IntSet(vals) => vals.iter().copied().min().unwrap_or(0),
        VarDomain::IntUnbounded => i64::MIN,
    }
}

fn domain_upper_bound(domain: &VarDomain) -> i64 {
    match domain {
        VarDomain::Bool => 1,
        VarDomain::IntRange(_, hi) => *hi,
        VarDomain::IntSet(vals) => vals.iter().copied().max().unwrap_or(0),
        VarDomain::IntUnbounded => i64::MAX,
    }
}

fn branching_satisfaction(
    result: &TranslationResult,
    config: &SolverConfig,
    plan: &[SearchPlanEntry],
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    let query_vars: Vec<String> = plan.iter().map(|e| e.smt_var.clone()).collect();
    let all_enumerable = plan.iter().all(|e| domain_is_enumerable(&e.domain));

    if !all_enumerable || plan.is_empty() {
        return branching_satisfaction_fallback(result, config, &query_vars, out);
    }

    let mut solver = IncrementalSolver::new(config, &result.declarations)?;

    match backtrack_search(&mut solver, plan, 0)? {
        SearchOutcome::Found => {
            // Solver stack has all branching assertions; last check-sat was sat.
            let vars = query_vars.join(" ");
            let values = solver.get_value(&vars)?;
            let dzn = format_dzn_solution(&values, &result.output_vars);
            write!(out, "{dzn}")?;
            writeln!(out, "----------")?;
            out.flush()?;
            Ok(1)
        }
        SearchOutcome::NotFound => {
            writeln!(out, "=====UNSATISFIABLE=====")?;
            out.flush()?;
            Ok(0)
        }
        SearchOutcome::Unknown => {
            writeln!(out, "=====UNKNOWN=====")?;
            out.flush()?;
            Ok(0)
        }
    }
}

fn domain_is_enumerable(domain: &VarDomain) -> bool {
    match domain {
        VarDomain::Bool => true,
        VarDomain::IntRange(lo, hi) => hi.saturating_sub(*lo) <= 1000,
        VarDomain::IntSet(vals) => vals.len() <= 1000,
        VarDomain::IntUnbounded => false,
    }
}

/// Backtracking search using an incremental ay solver.
///
/// Uses push/pop on the persistent ay process to add/remove assertions
/// at each depth level. When a satisfying path is found, the pushed scopes
/// remain on the solver stack for the caller to query variable values.
///
/// Returns `SearchOutcome::Found` if a satisfying path exists,
/// `SearchOutcome::NotFound` if all branches are UNSAT,
/// `SearchOutcome::Unknown` if no solution was found but at least one branch
/// returned UNKNOWN (soundness fix for #327).
fn backtrack_search(
    solver: &mut IncrementalSolver,
    plan: &[SearchPlanEntry],
    depth: usize,
) -> Result<SearchOutcome, SolverError> {
    if depth >= plan.len() {
        return Ok(SearchOutcome::Found);
    }

    let entry = &plan[depth];

    // Use binary split for split strategies on integer domains.
    // Bool domains fall through to per-value enumeration (can't use <= on booleans).
    if matches!(
        entry.val_choice,
        ValChoice::IndomainSplit | ValChoice::IndomainReverseSplit
    ) && !matches!(entry.domain, VarDomain::Bool)
    {
        let lo = domain_lower_bound(&entry.domain);
        let hi = domain_upper_bound(&entry.domain);
        if lo != i64::MIN && hi != i64::MAX {
            let reverse = entry.val_choice == ValChoice::IndomainReverseSplit;
            return split_branch(solver, plan, depth, lo, hi, reverse);
        }
    }

    let candidates = domain_candidates(&entry.domain, entry.val_choice);
    let mut found_unknown = false;

    for candidate in &candidates {
        let assertion = format!("(assert (= {} {}))\n", entry.smt_var, candidate);

        let status = solver.check_sat_incremental(&assertion)?;

        match status {
            CheckSatResult::Sat => match backtrack_search(solver, plan, depth + 1)? {
                SearchOutcome::Found => return Ok(SearchOutcome::Found),
                SearchOutcome::Unknown => {
                    found_unknown = true;
                    solver.pop()?;
                }
                SearchOutcome::NotFound => {
                    solver.pop()?;
                }
            },
            CheckSatResult::Unsat => {
                solver.pop()?;
            }
            CheckSatResult::Unknown => {
                found_unknown = true;
                solver.pop()?;
            }
        }
    }

    if found_unknown {
        Ok(SearchOutcome::Unknown)
    } else {
        Ok(SearchOutcome::NotFound)
    }
}

include!("split_branch.rs");

fn branching_satisfaction_fallback(
    result: &TranslationResult,
    config: &SolverConfig,
    query_vars: &[String],
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    let mut script = result.declarations.clone();
    script.push_str("(check-sat)\n");
    if !query_vars.is_empty() {
        let vars = query_vars.join(" ");
        script.push_str(&format!("(get-value ({vars}))\n"));
    }

    let output = run_ay(&script, config)?;
    let (status, lines) = parse_ay_output(&output)?;

    match status {
        CheckSatResult::Sat => {
            let values = parse_get_value(&lines)?;
            let dzn = format_dzn_solution(&values, &result.output_vars);
            write!(out, "{dzn}")?;
            writeln!(out, "----------")?;
            out.flush()?;
            Ok(1)
        }
        CheckSatResult::Unsat => {
            writeln!(out, "=====UNSATISFIABLE=====")?;
            out.flush()?;
            Ok(0)
        }
        CheckSatResult::Unknown => {
            writeln!(out, "=====UNKNOWN=====")?;
            out.flush()?;
            Ok(0)
        }
    }
}

#[cfg(test)]
#[path = "../branching_tests.rs"]
mod tests;
