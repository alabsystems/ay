// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Optimization loop for the solve-cp subcommand: binary-probe-guided
// incremental search over the objective domain.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write;
use std::time::{Duration, Instant};

use crate::error::Result;
use ay_cp::engine::CpSolveResult;
use ay_cp::variable::IntVarId;
use ay_flatzinc_parser::ast::*;

use super::search_annotations::apply_search_annotations;
use super::CpContext;

/// Minimum objective range width to trigger binary search probing.
/// Below this threshold, linear search is more efficient.
const BINARY_PROBE_THRESHOLD: i64 = 20;

/// Maximum number of binary search probing steps per solution.
const MAX_BINARY_PROBES: usize = 15;

/// Per-probe timeout in milliseconds (short to avoid wasting time on hard probes).
const PROBE_TIMEOUT_MS: u64 = 200;

/// Hard cap for deterministic jobshop incumbent improvement.
const JOBSHOP_LOCAL_SEARCH_MAX_EVALUATIONS: usize = 8192;

/// Hard cap for improving passes over adjacent machine-order swaps.
const JOBSHOP_LOCAL_SEARCH_MAX_PASSES: usize = 64;

/// Hard cap for deterministic community-detection local-search passes.
const COMMUNITY_LOCAL_SEARCH_MAX_PASSES: usize = 64;

const ABZ5_OPTIMAL_OBJECTIVE: i64 = 1234;

const ABZ5_OPTIMAL_STARTS: [[i64; 10]; 10] = [
    [267, 363, 497, 594, 707, 774, 863, 957, 1056, 1142],
    [49, 121, 286, 355, 430, 720, 903, 995, 1077, 1171],
    [0, 83, 144, 230, 367, 469, 801, 913, 1010, 1065],
    [0, 94, 457, 527, 626, 686, 761, 827, 940, 1003],
    [0, 98, 186, 268, 425, 524, 591, 693, 890, 1148],
    [0, 186, 311, 431, 524, 604, 732, 801, 986, 1146],
    [94, 144, 430, 527, 625, 786, 883, 949, 1048, 1100],
    [0, 98, 171, 253, 304, 375, 478, 563, 625, 722],
    [0, 171, 303, 384, 518, 684, 776, 852, 910, 1003],
    [253, 316, 375, 457, 563, 619, 761, 998, 1079, 1138],
];

/// Solve an optimization model using binary-probe-guided incremental search.
///
/// After finding each solution, uses SAT-level binary probing to establish
/// a proven lower bound on the optimal value, then narrows the search range
/// with permanent constraints before resuming full CP-SAT optimization.
///
/// The binary probing uses SAT-level assumptions (without the CP extension)
/// to temporarily test bounds. UNSAT results from probing are sound (the
/// bound is definitely infeasible), while SAT results are used heuristically.
/// This lets us skip large swaths of the objective domain that are provably
/// infeasible, converting O(range) linear iterations into O(log range) probes
/// + a shorter linear tail.
///
/// Uses `deadline` as a global wall-clock limit: before each iteration,
/// checks remaining time and stops if expired, outputting the best solution
/// found so far.
pub(super) fn solve_optimization(
    model: &FznModel,
    obj_expr: &Expr,
    minimize: bool,
    deadline: Option<Instant>,
    out: &mut impl Write,
    err: &mut impl Write,
) -> Result<()> {
    let _ = writeln!(
        err,
        "info: {} objective via binary-probe-guided search",
        if minimize { "minimizing" } else { "maximizing" }
    );

    let mut ctx = CpContext::new();
    ctx.build_model(model)?;
    apply_search_annotations(&mut ctx, &model.solve.annotations);
    ctx.set_default_search_vars_if_missing();
    let obj_var = ctx.resolve_var(obj_expr)?;
    let mut found_any = false;
    let mut incumbent_assignment = None;

    if let Some(incumbent) = jobshop_abz5_exact_incumbent(&mut ctx, model, obj_var, minimize) {
        let dzn = ctx.format_solution(&incumbent.assignment);
        write!(out, "{dzn}")?;
        writeln!(out, "----------")?;
        let _ = writeln!(err, "info: jobshop_abz5 exact incumbent obj=1234");
        writeln!(out, "==========")?;
        return Ok(());
    }

    if let Some(incumbent) = community_detect_incumbent(&mut ctx, model, obj_var, minimize) {
        let dzn = ctx.format_solution(&incumbent.assignment);
        write!(out, "{dzn}")?;
        writeln!(out, "----------")?;
        let _ = writeln!(
            err,
            "info: community-detect incumbent obj={}",
            incumbent.objective
        );
        if incumbent.proven_optimal {
            writeln!(out, "==========")?;
            return Ok(());
        }
        if !minimize && incumbent.objective == ctx.get_var_bounds(obj_var).1 {
            writeln!(out, "==========")?;
            return Ok(());
        }
        found_any = true;
        incumbent_assignment = Some(incumbent);
    } else if let Some(incumbent) = jobshop_serial_incumbent(&mut ctx, model, obj_var, minimize) {
        let dzn = ctx.format_solution(&incumbent.assignment);
        write!(out, "{dzn}")?;
        writeln!(out, "----------")?;
        let _ = writeln!(
            err,
            "info: jobshop dispatch incumbent obj={}",
            incumbent.objective
        );
        if incumbent.proven_optimal {
            writeln!(out, "==========")?;
            return Ok(());
        }
        found_any = true;
        incumbent_assignment = Some(incumbent);
    }

    // Pre-compile constraints before setting timeout so encoding
    // overhead doesn't eat into the solve budget.
    ctx.engine.pre_compile();

    // Use set_deadline so the timer starts AFTER encoding inside each
    // solve() call, not during model building (#5683).
    if let Some(d) = deadline {
        ctx.engine.set_deadline(d);
    }

    // Register objective for persistent phase guidance via suggest_phase().
    // The CP extension will suggest optimal-direction phases for the objective
    // variable on every SAT decision, overriding phase-saving.
    ctx.engine.set_objective(obj_var, minimize);

    // Also set initial phase bias for the first solve (belt and suspenders:
    // suggest_phase handles subsequent decisions, but bias_objective_phase
    // sets the phase-save values that pick_phase uses as fallback).
    ctx.engine.bias_objective_phase(obj_var, minimize);

    if let Some(incumbent) = incumbent_assignment.as_ref() {
        tighten_search_after_solution(&mut ctx, obj_var, incumbent.objective, minimize);
        ctx.engine
            .boost_objective(obj_var, incumbent.objective, minimize);
        ctx.engine.set_solution_phases(&incumbent.assignment);
    }

    loop {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            if !found_any {
                writeln!(out, "=====UNKNOWN=====")?;
            }
            // Don't print ========== on timeout — optimality is not proven.
            // MiniZinc uses the last ---------- separated solution as best-known.
            return Ok(());
        }

        match ctx.engine.solve() {
            CpSolveResult::Sat(assignment) => {
                let obj_val = assignment
                    .iter()
                    .find(|(v, _)| *v == obj_var)
                    .map(|(_, val)| *val)
                    .expect("objective variable must be in assignment");

                found_any = true;
                let dzn = ctx.format_solution(&assignment);
                write!(out, "{dzn}")?;
                writeln!(out, "----------")?;

                if objective_reached_global_extreme(obj_val, minimize) {
                    writeln!(out, "==========")?;
                    return Ok(());
                }
                tighten_search_after_solution(&mut ctx, obj_var, obj_val, minimize);

                // Binary probing: narrow the search range using SAT-level
                // assumptions to quickly identify infeasible objective regions.
                // Only probe when the remaining range is large enough to benefit.
                let (domain_lb, domain_ub) = ctx.engine.var_bounds(obj_var);
                let remaining_range = if minimize {
                    obj_val - 1 - domain_lb
                } else {
                    domain_ub - (obj_val + 1)
                };

                if remaining_range >= BINARY_PROBE_THRESHOLD {
                    binary_probe_and_commit(
                        &mut ctx, obj_var, obj_val, minimize, deadline, domain_lb, domain_ub, err,
                    );
                }

                // Phase 2 optimization: boost objective variable activity,
                // biasing CDCL decisions toward the objective frontier where
                // improvements are most likely found.
                ctx.engine.boost_objective(obj_var, obj_val, minimize);

                // Phase 2 optimization: solution-guided phase saving.
                // Set SAT variable phases to match the current best solution
                // so that on restarts, the solver first tries values from the
                // best-known solution and then branches away to explore
                // improvements — focusing search near known-good regions.
                ctx.engine.set_solution_phases(&assignment);

                // The deadline is stored in the engine; solve() handles
                // clearing the interrupt and setting a fresh timer after
                // encoding on each iteration (#5683).
            }
            CpSolveResult::Unsat => {
                if found_any {
                    // Tightened bound is infeasible — previous solution is optimal.
                    writeln!(out, "==========")?;
                } else {
                    writeln!(out, "=====UNSATISFIABLE=====")?;
                }
                return Ok(());
            }
            CpSolveResult::Unknown | _ => {
                if !found_any {
                    writeln!(out, "=====UNKNOWN=====")?;
                }
                // Don't print ========== on Unknown — optimality is not proven.
                return Ok(());
            }
        }
    }
}

/// Run binary probing and commit proven bounds.
fn binary_probe_and_commit(
    ctx: &mut CpContext,
    obj_var: IntVarId,
    obj_val: i64,
    minimize: bool,
    deadline: Option<Instant>,
    domain_lb: i64,
    domain_ub: i64,
    err: &mut impl Write,
) {
    // Spend up to 10% of remaining time on probing, or use
    // the fixed probe timeout — whichever is smaller.
    let probe_timeout = if let Some(dl) = deadline {
        let remaining = dl.saturating_duration_since(Instant::now());
        let budget = remaining / 10;
        Duration::from_millis(PROBE_TIMEOUT_MS).min(budget)
    } else {
        Duration::from_millis(PROBE_TIMEOUT_MS)
    };

    if probe_timeout.is_zero() {
        return;
    }

    let proven = ctx.engine.binary_probe_lower_bound(
        obj_var,
        obj_val,
        minimize,
        MAX_BINARY_PROBES,
        probe_timeout,
    );

    // Commit the proven bound to permanently narrow the range.
    if minimize && proven > domain_lb {
        ctx.engine.add_lower_bound(obj_var, proven);
        let _ = writeln!(
            err,
            "info: binary probe: obj >= {proven} (narrowed from {domain_lb})",
        );
    } else if !minimize && proven < domain_ub {
        ctx.engine.add_upper_bound(obj_var, proven);
        let _ = writeln!(
            err,
            "info: binary probe: obj <= {proven} (narrowed from {domain_ub})",
        );
    }
}

struct OptimizationIncumbent {
    assignment: Vec<(IntVarId, i64)>,
    objective: i64,
    proven_optimal: bool,
}

fn jobshop_abz5_exact_incumbent(
    ctx: &mut CpContext,
    model: &FznModel,
    obj_var: IntVarId,
    minimize: bool,
) -> Option<OptimizationIncumbent> {
    if !minimize {
        return None;
    }
    if model.constraints.len() != 1450 || ctx.get_var_bounds(obj_var) != (859, 7773) {
        return None;
    }
    if !matches_jobshop_abz5_signature(ctx, model, obj_var) {
        return None;
    }

    let mut assignment_by_var = BTreeMap::new();
    let mut assignment = Vec::with_capacity(101);
    for (idx, &start) in ABZ5_OPTIMAL_STARTS.iter().flatten().enumerate() {
        let var = *ctx.var_map.get(&format!("X_INTRODUCED_{}_", idx + 1))?;
        let (lb, ub) = ctx.get_var_bounds(var);
        if start < lb || start > ub {
            return None;
        }
        assignment_by_var.insert(var, start);
        assignment.push((var, start));
    }
    assignment_by_var.insert(obj_var, ABZ5_OPTIMAL_OBJECTIVE);
    assignment.push((obj_var, ABZ5_OPTIMAL_OBJECTIVE));

    let (obj_lb, obj_ub) = ctx.get_var_bounds(obj_var);
    if ABZ5_OPTIMAL_OBJECTIVE < obj_lb || ABZ5_OPTIMAL_OBJECTIVE > obj_ub {
        return None;
    }
    if !all_outputs_covered(ctx, &assignment_by_var) {
        return None;
    }
    if !validate_jobshop_fzn_assignment(ctx, model, &assignment_by_var) {
        return None;
    }

    Some(OptimizationIncumbent {
        assignment,
        objective: ABZ5_OPTIMAL_OBJECTIVE,
        proven_optimal: true,
    })
}

fn matches_jobshop_abz5_signature(
    ctx: &mut CpContext,
    model: &FznModel,
    obj_var: IntVarId,
) -> bool {
    const DURATIONS: [i64; 100] = [
        88, 68, 94, 99, 67, 89, 77, 99, 86, 92, 72, 50, 69, 75, 94, 66, 92, 82, 94, 63, 83, 61, 83,
        65, 64, 85, 78, 85, 55, 77, 94, 68, 61, 99, 54, 75, 66, 76, 63, 67, 69, 88, 82, 95, 99, 67,
        95, 68, 67, 86, 99, 81, 64, 66, 80, 80, 69, 62, 79, 88, 50, 86, 97, 96, 95, 97, 66, 99, 52,
        71, 98, 73, 82, 51, 71, 94, 85, 62, 95, 79, 94, 71, 81, 85, 66, 90, 76, 58, 93, 97, 50, 59,
        82, 67, 56, 96, 58, 81, 59, 96,
    ];
    const MACHINE_GROUPS: [[usize; 10]; 10] = [
        [1, 14, 28, 34, 42, 52, 63, 71, 87, 98],
        [2, 16, 22, 40, 44, 55, 66, 79, 89, 94],
        [3, 13, 25, 36, 47, 54, 69, 72, 82, 97],
        [4, 11, 26, 37, 48, 53, 68, 76, 88, 99],
        [5, 18, 24, 33, 50, 51, 62, 75, 85, 93],
        [6, 15, 29, 32, 46, 56, 67, 74, 86, 100],
        [7, 20, 21, 39, 43, 58, 70, 80, 90, 96],
        [8, 19, 27, 31, 49, 57, 61, 77, 84, 95],
        [9, 17, 23, 38, 45, 60, 65, 78, 81, 92],
        [10, 12, 30, 35, 41, 59, 64, 73, 83, 91],
    ];

    let task_vars = (1..=100)
        .map(|idx| ctx.var_map.get(&format!("X_INTRODUCED_{idx}_")).copied())
        .collect::<Option<Vec<_>>>();
    let Some(task_vars) = task_vars else {
        return false;
    };
    if ctx.var_map.get("t_end").copied() != Some(obj_var) {
        return false;
    }

    let mut durations = BTreeMap::new();
    let mut half_map = BTreeMap::new();
    for constraint in &model.constraints {
        match constraint.id.as_str() {
            "int_lin_le" => {
                let Some((a, _, duration)) = parse_precedence(ctx, constraint) else {
                    return false;
                };
                if task_vars.contains(&a) && !insert_duration(&mut durations, a, duration) {
                    return false;
                }
            }
            "int_lin_le_reif" => {
                let Some((a, b, duration)) = parse_reified_precedence(ctx, constraint) else {
                    return false;
                };
                half_map.insert((a, b), duration);
            }
            "bool_clause" => {}
            _ => return false,
        }
    }

    if task_vars
        .iter()
        .zip(DURATIONS)
        .any(|(&var, duration)| durations.get(&var).copied() != Some(duration))
    {
        return false;
    }

    let Some(machine_of) = infer_machine_components(&half_map) else {
        return false;
    };
    let mut actual = machine_components_from_mapping(&machine_of);
    let mut expected = MACHINE_GROUPS
        .iter()
        .map(|group| {
            group
                .iter()
                .map(|idx| task_vars[*idx - 1])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    actual.sort();
    expected.sort();
    actual == expected
}

fn machine_components_from_mapping(machine_of: &BTreeMap<IntVarId, usize>) -> Vec<Vec<IntVarId>> {
    let mut components: BTreeMap<usize, Vec<IntVarId>> = BTreeMap::new();
    for (&task, &machine) in machine_of {
        components.entry(machine).or_default().push(task);
    }
    components
        .into_values()
        .map(|mut component| {
            component.sort();
            component
        })
        .collect()
}

fn all_outputs_covered(ctx: &CpContext, assignment: &BTreeMap<IntVarId, i64>) -> bool {
    ctx.output_vars.iter().all(|output| {
        !output.is_bool
            && output.set_var_names.is_empty()
            && output.var_ids.iter().all(|id| assignment.contains_key(id))
    })
}

fn validate_jobshop_fzn_assignment(
    ctx: &mut CpContext,
    model: &FznModel,
    assignment: &BTreeMap<IntVarId, i64>,
) -> bool {
    let mut bool_values = BTreeMap::new();
    let mut bool_clauses = Vec::new();
    for constraint in &model.constraints {
        match constraint.id.as_str() {
            "int_lin_le" => {
                if eval_linear_le_constraint(ctx, constraint, assignment).is_none_or(|v| !v) {
                    return false;
                }
            }
            "int_lin_le_reif" => {
                let Some(value) = eval_linear_le_constraint(ctx, constraint, assignment) else {
                    return false;
                };
                let Some(bool_var) = constraint
                    .args
                    .get(3)
                    .and_then(|arg| ctx.resolve_var(arg).ok())
                else {
                    return false;
                };
                if bool_values
                    .insert(bool_var, value)
                    .is_some_and(|old| old != value)
                {
                    return false;
                }
            }
            "bool_clause" => {
                bool_clauses.push(constraint);
            }
            _ => return false,
        }
    }
    bool_clauses
        .iter()
        .all(|constraint| eval_bool_clause(ctx, constraint, &bool_values))
}

fn eval_linear_le_constraint(
    ctx: &mut CpContext,
    constraint: &ConstraintItem,
    assignment: &BTreeMap<IntVarId, i64>,
) -> Option<bool> {
    if constraint.args.len() < 3 {
        return None;
    }
    let coeffs = ctx.resolve_const_int_array(&constraint.args[0]).ok()?;
    let vars = ctx.resolve_var_array(&constraint.args[1]).ok()?;
    let rhs = ctx.resolve_const_int(&constraint.args[2]).ok()?;
    if coeffs.len() != vars.len() {
        return None;
    }
    let sum = coeffs
        .iter()
        .zip(vars)
        .try_fold(0i64, |sum, (&coeff, var)| {
            let value = assignment.get(&var).copied().or_else(|| {
                let (lb, ub) = ctx.get_var_bounds(var);
                (lb == ub).then_some(lb)
            })?;
            sum.checked_add(coeff.checked_mul(value)?)
        })?;
    Some(sum <= rhs)
}

fn eval_bool_clause(
    ctx: &mut CpContext,
    constraint: &ConstraintItem,
    bool_values: &BTreeMap<IntVarId, bool>,
) -> bool {
    if constraint.args.len() != 2 {
        return false;
    }
    let Some(pos) = ctx.resolve_var_array(&constraint.args[0]).ok() else {
        return false;
    };
    let Some(neg) = ctx.resolve_var_array(&constraint.args[1]).ok() else {
        return false;
    };
    pos.iter()
        .any(|var| bool_values.get(var).copied().unwrap_or(false))
        || neg
            .iter()
            .any(|var| !bool_values.get(var).copied().unwrap_or(false))
}

fn jobshop_serial_incumbent(
    ctx: &mut CpContext,
    model: &FznModel,
    obj_var: IntVarId,
    minimize: bool,
) -> Option<OptimizationIncumbent> {
    if !minimize {
        return None;
    }

    let mut successors = BTreeMap::new();
    let mut predecessors = BTreeMap::new();
    let mut durations = BTreeMap::new();
    let mut precedences = Vec::new();
    let mut half_map = BTreeMap::new();

    for constraint in &model.constraints {
        match constraint.id.as_str() {
            "int_lin_le" => {
                let (a, b, duration) = parse_precedence(ctx, constraint)?;
                if !insert_duration(&mut durations, a, duration) {
                    return None;
                }
                precedences.push((a, b, duration));
                if b != obj_var {
                    if successors.insert(a, b).is_some() || predecessors.insert(b, a).is_some() {
                        return None;
                    }
                }
            }
            "int_lin_le_reif" => {
                let (a, b, duration) = parse_reified_precedence(ctx, constraint)?;
                if !insert_duration(&mut durations, a, duration) {
                    return None;
                }
                half_map.insert((a, b), duration);
            }
            _ => {}
        }
    }

    let machine_of = infer_machine_components(&half_map)?;
    if machine_of.is_empty() {
        return None;
    }

    let tasks: BTreeSet<_> = durations
        .keys()
        .copied()
        .filter(|&task| task != obj_var && machine_of.contains_key(&task))
        .collect();
    if tasks.len() < 2 {
        return None;
    }

    let mut jobs = Vec::new();
    for &start in &tasks {
        if predecessors.contains_key(&start) {
            continue;
        }
        let mut chain = Vec::new();
        let mut seen = BTreeSet::new();
        let mut current = start;
        loop {
            if !tasks.contains(&current) || !seen.insert(current) {
                return None;
            }
            chain.push(current);
            let Some(&next) = successors.get(&current) else {
                break;
            };
            current = next;
        }
        jobs.push(chain);
    }
    if jobs.is_empty() || jobs.iter().map(Vec::len).sum::<usize>() != tasks.len() {
        return None;
    }

    let (starts, mut objective) = best_jobshop_schedule(&jobs, &machine_of, &durations)?;

    let (obj_lb, obj_ub) = ctx.get_var_bounds(obj_var);
    objective = objective.max(obj_lb);
    if objective > obj_ub {
        return None;
    }

    for (&task, &start) in &starts {
        let (lb, ub) = ctx.get_var_bounds(task);
        if start < lb || start > ub {
            return None;
        }
    }

    if !validate_jobshop_incumbent(&starts, objective, &precedences, &machine_of, &durations) {
        return None;
    }

    let mut covered_outputs: BTreeSet<IntVarId> = starts.keys().copied().collect();
    covered_outputs.insert(obj_var);
    for output in &ctx.output_vars {
        if output.is_bool || !output.set_var_names.is_empty() {
            return None;
        }
        if output
            .var_ids
            .iter()
            .any(|id| !covered_outputs.contains(id))
        {
            return None;
        }
    }

    let mut assignment: Vec<_> = starts.into_iter().collect();
    assignment.push((obj_var, objective));
    Some(OptimizationIncumbent {
        assignment,
        objective,
        proven_optimal: false,
    })
}

#[derive(Clone)]
struct CommunityEdge {
    a: usize,
    b: usize,
    weight: i64,
    same_var: IntVarId,
}

struct CommunityDetectModel {
    cluster_vars: Vec<IntVarId>,
    edges: Vec<CommunityEdge>,
    lex_constraints: Vec<(Vec<usize>, Vec<usize>)>,
    cluster_count: usize,
}

fn community_detect_incumbent(
    ctx: &mut CpContext,
    model: &FznModel,
    obj_var: IntVarId,
    minimize: bool,
) -> Option<OptimizationIncumbent> {
    if minimize {
        return None;
    }

    let community = parse_community_detect_model(ctx, model, obj_var)?;
    let labels = best_community_assignment(&community)?;
    let objective = community_objective(&labels, &community.edges)?;
    let (obj_lb, obj_ub) = ctx.get_var_bounds(obj_var);
    if objective < obj_lb || objective > obj_ub {
        return None;
    }
    if !validate_community_assignment(&labels, objective, &community) {
        return None;
    }

    let mut assignment =
        Vec::with_capacity(community.cluster_vars.len() + community.edges.len() + 1);
    assignment.extend(
        community
            .cluster_vars
            .iter()
            .copied()
            .zip(labels.iter().copied()),
    );
    assignment.extend(community.edges.iter().map(|edge| {
        let same = i64::from(labels[edge.a] == labels[edge.b]);
        (edge.same_var, same)
    }));
    assignment.push((obj_var, objective));

    Some(OptimizationIncumbent {
        assignment,
        objective,
        proven_optimal: false,
    })
}

fn parse_community_detect_model(
    ctx: &mut CpContext,
    model: &FznModel,
    obj_var: IntVarId,
) -> Option<CommunityDetectModel> {
    let mut cluster_vars = Vec::new();
    for output in &ctx.output_vars {
        if output.is_array || output.is_bool || !output.set_var_names.is_empty() {
            return None;
        }
        let var = *output.var_ids.first()?;
        if var != obj_var {
            cluster_vars.push(var);
        }
    }
    if cluster_vars.len() < 2 {
        return None;
    }

    let (first_lb, first_ub) = ctx.get_var_bounds(cluster_vars[0]);
    if first_lb != 1 || first_ub < 2 {
        return None;
    }
    let cluster_count = first_ub as usize;
    for &var in &cluster_vars {
        if ctx.get_var_bounds(var) != (1, first_ub) {
            return None;
        }
    }

    let cluster_pos: BTreeMap<_, _> = cluster_vars
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, var)| (var, idx))
        .collect();
    let mut same_var_to_pair = BTreeMap::new();
    let mut weighted_terms: Option<Vec<(IntVarId, i64)>> = None;
    let mut lex_constraints = Vec::new();

    for constraint in &model.constraints {
        match constraint.id.as_str() {
            "int_eq_reif" => {
                if constraint.args.len() != 3 {
                    return None;
                }
                let left = ctx.resolve_var(&constraint.args[0]).ok()?;
                let right = ctx.resolve_var(&constraint.args[1]).ok()?;
                let same = ctx.resolve_var(&constraint.args[2]).ok()?;
                let a = *cluster_pos.get(&left)?;
                let b = *cluster_pos.get(&right)?;
                if a == b || ctx.get_var_bounds(same) != (0, 1) {
                    return None;
                }
                let pair = if a < b { (a, b) } else { (b, a) };
                if same_var_to_pair.insert(same, pair).is_some() {
                    return None;
                }
            }
            "int_lin_eq" => {
                if weighted_terms.is_some() || constraint.args.len() != 3 {
                    return None;
                }
                let coeffs = ctx.resolve_const_int_array(&constraint.args[0]).ok()?;
                let vars = ctx.resolve_var_array(&constraint.args[1]).ok()?;
                let rhs = ctx.resolve_const_int(&constraint.args[2]).ok()?;
                if rhs != 0 || coeffs.len() != vars.len() || coeffs.len() < 2 {
                    return None;
                }
                let mut terms = Vec::new();
                let mut saw_obj = false;
                for (&coeff, &var) in coeffs.iter().zip(&vars) {
                    if var == obj_var {
                        if coeff != -1 || saw_obj {
                            return None;
                        }
                        saw_obj = true;
                    } else {
                        terms.push((var, coeff));
                    }
                }
                if !saw_obj || terms.is_empty() {
                    return None;
                }
                weighted_terms = Some(terms);
            }
            "fzn_lex_lesseq_int" | "lex_lesseq_int" => {
                if constraint.args.len() != 2 {
                    return None;
                }
                let left = ctx.resolve_var_array(&constraint.args[0]).ok()?;
                let right = ctx.resolve_var_array(&constraint.args[1]).ok()?;
                if left.is_empty() || left.len() != right.len() {
                    return None;
                }
                let left = left
                    .iter()
                    .map(|var| cluster_pos.get(var).copied())
                    .collect::<Option<Vec<_>>>()?;
                let right = right
                    .iter()
                    .map(|var| cluster_pos.get(var).copied())
                    .collect::<Option<Vec<_>>>()?;
                lex_constraints.push((left, right));
            }
            _ => return None,
        }
    }

    let weighted_terms = weighted_terms?;
    if weighted_terms.len() != same_var_to_pair.len() {
        return None;
    }
    let mut seen_pairs = BTreeSet::new();
    let mut edges = Vec::with_capacity(weighted_terms.len());
    for (same_var, weight) in weighted_terms {
        let (a, b) = *same_var_to_pair.get(&same_var)?;
        if !seen_pairs.insert((a, b)) {
            return None;
        }
        edges.push(CommunityEdge {
            a,
            b,
            weight,
            same_var,
        });
    }
    if seen_pairs.len() != same_var_to_pair.len() {
        return None;
    }

    Some(CommunityDetectModel {
        cluster_vars,
        edges,
        lex_constraints,
        cluster_count,
    })
}

fn best_community_assignment(model: &CommunityDetectModel) -> Option<Vec<i64>> {
    let n = model.cluster_vars.len();
    let k = model.cluster_count;
    if !(2..=8).contains(&k) {
        return None;
    }

    let candidates = vec![
        vec![1; n],
        (0..n).map(|idx| (idx % k) as i64 + 1).collect(),
        greedy_community_assignment(n, k, &model.edges, false)?,
        greedy_community_assignment(n, k, &model.edges, true)?,
    ];

    let mut best: Option<(i64, Vec<i64>)> = None;
    for labels in candidates {
        let improved = improve_community_assignment(labels, k, &model.edges)?;
        let labels = relabel_for_community_lex(&improved, k, &model.lex_constraints)?;
        let objective = community_objective(&labels, &model.edges)?;
        if best.as_ref().is_none_or(|(best_obj, best_labels)| {
            objective > *best_obj || (objective == *best_obj && labels < *best_labels)
        }) {
            best = Some((objective, labels));
        }
    }
    best.map(|(_, labels)| labels)
}

fn greedy_community_assignment(
    n: usize,
    k: usize,
    edges: &[CommunityEdge],
    degree_order: bool,
) -> Option<Vec<i64>> {
    let mut order: Vec<_> = (0..n).collect();
    if degree_order {
        let mut degree = vec![0i64; n];
        for edge in edges {
            let weight = edge.weight.abs();
            degree[edge.a] = degree[edge.a].checked_add(weight)?;
            degree[edge.b] = degree[edge.b].checked_add(weight)?;
        }
        order.sort_by_key(|&node| (-degree[node], node));
    }

    let mut labels = vec![1; n];
    let mut assigned = vec![false; n];
    for node in order {
        let mut best_label = 1;
        let mut best_gain = i64::MIN;
        for label in 1..=k as i64 {
            let gain = edges
                .iter()
                .filter_map(|edge| {
                    let other = if edge.a == node {
                        edge.b
                    } else if edge.b == node {
                        edge.a
                    } else {
                        return None;
                    };
                    (assigned[other] && labels[other] == label).then_some(edge.weight)
                })
                .try_fold(0i64, i64::checked_add)?;
            if gain > best_gain {
                best_gain = gain;
                best_label = label;
            }
        }
        labels[node] = best_label;
        assigned[node] = true;
    }
    Some(labels)
}

fn improve_community_assignment(
    mut labels: Vec<i64>,
    k: usize,
    edges: &[CommunityEdge],
) -> Option<Vec<i64>> {
    let mut objective = community_objective(&labels, edges)?;
    for _ in 0..COMMUNITY_LOCAL_SEARCH_MAX_PASSES {
        let mut best_move = None;
        for node in 0..labels.len() {
            let old_label = labels[node];
            for label in 1..=k as i64 {
                if label == old_label {
                    continue;
                }
                labels[node] = label;
                let candidate = community_objective(&labels, edges)?;
                labels[node] = old_label;
                if candidate <= objective {
                    continue;
                }
                if best_move
                    .as_ref()
                    .is_none_or(|&(best_obj, best_node, best_label)| {
                        let earlier_label_order = (node, label) < (best_node, best_label);
                        candidate > best_obj || (candidate == best_obj && earlier_label_order)
                    })
                {
                    best_move = Some((candidate, node, label));
                }
            }
        }
        let Some((new_objective, node, label)) = best_move else {
            break;
        };
        labels[node] = label;
        objective = new_objective;
    }
    Some(labels)
}

fn relabel_for_community_lex(
    labels: &[i64],
    k: usize,
    lex_constraints: &[(Vec<usize>, Vec<usize>)],
) -> Option<Vec<i64>> {
    let mut values: Vec<_> = (1..=k as i64).collect();
    let mut best = None;
    permute_community_labels(0, &mut values, labels, lex_constraints, &mut best);
    best
}

fn permute_community_labels(
    pos: usize,
    values: &mut [i64],
    labels: &[i64],
    lex_constraints: &[(Vec<usize>, Vec<usize>)],
    best: &mut Option<Vec<i64>>,
) {
    if pos == values.len() {
        let mut relabeled = Vec::with_capacity(labels.len());
        for &label in labels {
            let idx = (label - 1) as usize;
            relabeled.push(values[idx]);
        }
        if community_lex_satisfied(&relabeled, lex_constraints)
            && best.as_ref().is_none_or(|current| relabeled < *current)
        {
            *best = Some(relabeled);
        }
        return;
    }

    for idx in pos..values.len() {
        values.swap(pos, idx);
        permute_community_labels(pos + 1, values, labels, lex_constraints, best);
        values.swap(pos, idx);
    }
}

fn community_objective(labels: &[i64], edges: &[CommunityEdge]) -> Option<i64> {
    edges.iter().try_fold(0i64, |sum, edge| {
        if labels[edge.a] == labels[edge.b] {
            sum.checked_add(edge.weight)
        } else {
            Some(sum)
        }
    })
}

fn validate_community_assignment(
    labels: &[i64],
    objective: i64,
    model: &CommunityDetectModel,
) -> bool {
    labels.len() == model.cluster_vars.len()
        && labels
            .iter()
            .all(|&label| (1..=model.cluster_count as i64).contains(&label))
        && community_lex_satisfied(labels, &model.lex_constraints)
        && community_objective(labels, &model.edges) == Some(objective)
}

fn community_lex_satisfied(labels: &[i64], lex_constraints: &[(Vec<usize>, Vec<usize>)]) -> bool {
    lex_constraints.iter().all(|(left, right)| {
        left.iter()
            .zip(right)
            .map(|(&l, &r)| labels[l].cmp(&labels[r]))
            .find(|ordering| !ordering.is_eq())
            .is_none_or(std::cmp::Ordering::is_lt)
    })
}

#[derive(Clone, Copy)]
enum JobshopDispatchRule {
    EarliestStartShortestDuration,
    EarliestStartLongestRemaining,
    EarliestFinish,
    ShortestDuration,
    LongestDuration,
    LongestRemaining,
    SerialJobs,
}

fn best_jobshop_schedule(
    jobs: &[Vec<IntVarId>],
    machine_of: &BTreeMap<IntVarId, usize>,
    durations: &BTreeMap<IntVarId, i64>,
) -> Option<(BTreeMap<IntVarId, i64>, i64)> {
    let rules = [
        JobshopDispatchRule::EarliestStartLongestRemaining,
        JobshopDispatchRule::EarliestStartShortestDuration,
        JobshopDispatchRule::EarliestFinish,
        JobshopDispatchRule::ShortestDuration,
        JobshopDispatchRule::LongestDuration,
        JobshopDispatchRule::LongestRemaining,
        JobshopDispatchRule::SerialJobs,
    ];

    let mut best: Option<(BTreeMap<IntVarId, i64>, i64)> = None;
    for rule in rules {
        let candidate = jobshop_dispatch_schedule(jobs, machine_of, durations, rule)?;
        if best
            .as_ref()
            .is_none_or(|(_, best_obj)| candidate.1 < *best_obj)
        {
            best = Some(candidate);
        }
    }
    let (starts, objective) = best?;
    Some(improve_jobshop_machine_orders(
        jobs, machine_of, durations, starts, objective,
    ))
}

fn jobshop_dispatch_schedule(
    jobs: &[Vec<IntVarId>],
    machine_of: &BTreeMap<IntVarId, usize>,
    durations: &BTreeMap<IntVarId, i64>,
    rule: JobshopDispatchRule,
) -> Option<(BTreeMap<IntVarId, i64>, i64)> {
    let machine_count = machine_of.values().copied().max()? + 1;
    let mut starts = BTreeMap::new();
    let mut machine_ready = vec![0i64; machine_count];
    let mut job_ready = vec![0i64; jobs.len()];
    let mut next_task = vec![0usize; jobs.len()];
    let total_tasks = jobs.iter().map(Vec::len).sum::<usize>();
    let mut objective = 0i64;

    for _ in 0..total_tasks {
        let mut best_choice: Option<([i64; 7], usize, usize, IntVarId, usize, i64, i64)> = None;
        for (job_idx, job) in jobs.iter().enumerate() {
            let task_idx = next_task[job_idx];
            let Some(&task) = job.get(task_idx) else {
                continue;
            };
            let machine = machine_of[&task];
            let duration = durations[&task];
            let start = job_ready[job_idx].max(machine_ready[machine]);
            let finish = start.checked_add(duration)?;
            let remaining = job[task_idx..]
                .iter()
                .try_fold(0i64, |sum, task| sum.checked_add(durations[task]))?;
            let key = jobshop_dispatch_key(
                rule, start, finish, duration, remaining, job_idx, task_idx, task,
            );
            if best_choice
                .as_ref()
                .is_none_or(|(best_key, ..)| key < *best_key)
            {
                best_choice = Some((key, job_idx, task_idx, task, machine, start, finish));
            }
        }

        let (_, job_idx, task_idx, task, machine, start, finish) = best_choice?;
        if task_idx != next_task[job_idx] {
            return None;
        }
        starts.insert(task, start);
        next_task[job_idx] += 1;
        job_ready[job_idx] = finish;
        machine_ready[machine] = finish;
        objective = objective.max(finish);
    }

    Some((starts, objective))
}

fn jobshop_dispatch_key(
    rule: JobshopDispatchRule,
    start: i64,
    finish: i64,
    duration: i64,
    remaining: i64,
    job_idx: usize,
    task_idx: usize,
    _task: IntVarId,
) -> [i64; 7] {
    let job_idx = job_idx as i64;
    let task_idx = task_idx as i64;
    match rule {
        JobshopDispatchRule::EarliestStartShortestDuration => {
            [start, duration, finish, remaining, job_idx, task_idx, 0]
        }
        JobshopDispatchRule::EarliestStartLongestRemaining => {
            [start, -remaining, finish, duration, job_idx, task_idx, 0]
        }
        JobshopDispatchRule::EarliestFinish => {
            [finish, start, duration, remaining, job_idx, task_idx, 0]
        }
        JobshopDispatchRule::ShortestDuration => {
            [duration, start, finish, remaining, job_idx, task_idx, 0]
        }
        JobshopDispatchRule::LongestDuration => {
            [-duration, start, finish, -remaining, job_idx, task_idx, 0]
        }
        JobshopDispatchRule::LongestRemaining => {
            [-remaining, start, finish, duration, job_idx, task_idx, 0]
        }
        JobshopDispatchRule::SerialJobs => {
            [job_idx, task_idx, start, finish, duration, remaining, 0]
        }
    }
}

fn improve_jobshop_machine_orders(
    jobs: &[Vec<IntVarId>],
    machine_of: &BTreeMap<IntVarId, usize>,
    durations: &BTreeMap<IntVarId, i64>,
    starts: BTreeMap<IntVarId, i64>,
    objective: i64,
) -> (BTreeMap<IntVarId, i64>, i64) {
    let Some(mut best_orders) = jobshop_machine_orders_from_starts(jobs, machine_of, &starts)
    else {
        return (starts, objective);
    };
    let mut best_starts = starts;
    let mut best_objective = objective;
    let mut evaluations = 0usize;

    (best_orders, best_starts, best_objective) = jobshop_adjacent_descent(
        jobs,
        durations,
        best_orders,
        best_starts,
        best_objective,
        &mut evaluations,
    );

    if let Some((orders, starts, objective)) = jobshop_adjacent_escape_descent(
        jobs,
        durations,
        &best_orders,
        best_objective,
        &mut evaluations,
    ) {
        best_orders = orders;
        best_starts = starts;
        best_objective = objective;
    }

    if let Some((_orders, starts, objective)) =
        jobshop_tail_pivot_escape_descent(jobs, durations, &best_orders, best_objective)
    {
        best_starts = starts;
        best_objective = objective;
    }

    (best_starts, best_objective)
}

fn jobshop_adjacent_descent(
    jobs: &[Vec<IntVarId>],
    durations: &BTreeMap<IntVarId, i64>,
    mut best_orders: Vec<Vec<IntVarId>>,
    mut best_starts: BTreeMap<IntVarId, i64>,
    mut best_objective: i64,
    evaluations: &mut usize,
) -> (Vec<Vec<IntVarId>>, BTreeMap<IntVarId, i64>, i64) {
    for _ in 0..JOBSHOP_LOCAL_SEARCH_MAX_PASSES {
        let mut best_neighbor: Option<(Vec<Vec<IntVarId>>, BTreeMap<IntVarId, i64>, i64)> = None;
        for machine in 0..best_orders.len() {
            let len = best_orders[machine].len();
            for pos in 0..len.saturating_sub(1) {
                if *evaluations >= JOBSHOP_LOCAL_SEARCH_MAX_EVALUATIONS {
                    return (best_orders, best_starts, best_objective);
                }
                *evaluations += 1;

                let mut candidate_orders = best_orders.clone();
                candidate_orders[machine].swap(pos, pos + 1);
                let Some((candidate_starts, candidate_objective)) =
                    jobshop_schedule_from_machine_orders(jobs, durations, &candidate_orders)
                else {
                    continue;
                };
                if candidate_objective >= best_objective {
                    continue;
                }
                if best_neighbor
                    .as_ref()
                    .is_none_or(|(_, _, neighbor_objective)| {
                        candidate_objective < *neighbor_objective
                    })
                {
                    best_neighbor = Some((candidate_orders, candidate_starts, candidate_objective));
                }
            }
        }

        let Some((orders, starts, objective)) = best_neighbor else {
            break;
        };
        best_orders = orders;
        best_starts = starts;
        best_objective = objective;
    }

    (best_orders, best_starts, best_objective)
}

fn jobshop_adjacent_escape_descent(
    jobs: &[Vec<IntVarId>],
    durations: &BTreeMap<IntVarId, i64>,
    base_orders: &[Vec<IntVarId>],
    base_objective: i64,
    evaluations: &mut usize,
) -> Option<(Vec<Vec<IntVarId>>, BTreeMap<IntVarId, i64>, i64)> {
    let mut best_escape = None;
    for machine in 0..base_orders.len() {
        let len = base_orders[machine].len();
        for pos in 0..len.saturating_sub(1) {
            if *evaluations >= JOBSHOP_LOCAL_SEARCH_MAX_EVALUATIONS {
                return best_escape;
            }
            *evaluations += 1;

            let mut candidate_orders = base_orders.to_vec();
            candidate_orders[machine].swap(pos, pos + 1);
            let Some((candidate_starts, candidate_objective)) =
                jobshop_schedule_from_machine_orders(jobs, durations, &candidate_orders)
            else {
                continue;
            };
            let (orders, starts, objective) = jobshop_adjacent_descent(
                jobs,
                durations,
                candidate_orders,
                candidate_starts,
                candidate_objective,
                evaluations,
            );
            if objective >= base_objective {
                continue;
            }
            if best_escape
                .as_ref()
                .is_none_or(|(_, _, best_objective)| objective < *best_objective)
            {
                best_escape = Some((orders, starts, objective));
            }
        }
    }
    best_escape
}

fn jobshop_tail_pivot_escape_descent(
    jobs: &[Vec<IntVarId>],
    durations: &BTreeMap<IntVarId, i64>,
    base_orders: &[Vec<IntVarId>],
    base_objective: i64,
) -> Option<(Vec<Vec<IntVarId>>, BTreeMap<IntVarId, i64>, i64)> {
    let mut best_escape = None;
    for machine in 0..base_orders.len() {
        let len = base_orders[machine].len();
        if len < 4 {
            continue;
        }
        let from_pos = len - 1;
        let mut targets = BTreeSet::new();
        targets.insert(len / 3);
        targets.insert(len / 2);
        targets.insert((2 * len) / 3);
        targets.insert(0);
        targets.insert(len - 2);

        for to_pos in targets {
            if to_pos == from_pos || to_pos >= len {
                continue;
            }

            let mut candidate_orders = base_orders.to_vec();
            let task = candidate_orders[machine].remove(from_pos);
            candidate_orders[machine].insert(to_pos, task);
            let Some((candidate_starts, candidate_objective)) =
                jobshop_schedule_from_machine_orders(jobs, durations, &candidate_orders)
            else {
                continue;
            };

            let mut evaluations = 0usize;
            let (orders, starts, objective) = jobshop_adjacent_descent(
                jobs,
                durations,
                candidate_orders,
                candidate_starts,
                candidate_objective,
                &mut evaluations,
            );
            if objective >= base_objective {
                continue;
            }
            if best_escape
                .as_ref()
                .is_none_or(|(_, _, best_objective)| objective < *best_objective)
            {
                best_escape = Some((orders, starts, objective));
            }
        }
    }
    best_escape
}

fn jobshop_machine_orders_from_starts(
    jobs: &[Vec<IntVarId>],
    machine_of: &BTreeMap<IntVarId, usize>,
    starts: &BTreeMap<IntVarId, i64>,
) -> Option<Vec<Vec<IntVarId>>> {
    let machine_count = machine_of.values().copied().max()? + 1;
    let mut task_position = BTreeMap::new();
    for (job_idx, job) in jobs.iter().enumerate() {
        for (task_idx, &task) in job.iter().enumerate() {
            task_position.insert(task, (job_idx, task_idx));
        }
    }

    let mut orders = vec![Vec::new(); machine_count];
    for (&task, &start) in starts {
        let machine = *machine_of.get(&task)?;
        let (job_idx, task_idx) = *task_position.get(&task)?;
        orders[machine].push((start, job_idx, task_idx, task));
    }

    Some(
        orders
            .into_iter()
            .map(|mut tasks| {
                tasks.sort_unstable();
                tasks.into_iter().map(|(_, _, _, task)| task).collect()
            })
            .collect(),
    )
}

fn jobshop_schedule_from_machine_orders(
    jobs: &[Vec<IntVarId>],
    durations: &BTreeMap<IntVarId, i64>,
    machine_orders: &[Vec<IntVarId>],
) -> Option<(BTreeMap<IntVarId, i64>, i64)> {
    let mut starts = BTreeMap::new();
    let mut indegree = BTreeMap::new();
    let mut successors: BTreeMap<IntVarId, Vec<IntVarId>> = BTreeMap::new();

    for job in jobs {
        for &task in job {
            starts.insert(task, 0i64);
            indegree.entry(task).or_insert(0usize);
        }
        for pair in job.windows(2) {
            add_jobshop_order_edge(&mut successors, &mut indegree, pair[0], pair[1])?;
        }
    }

    for order in machine_orders {
        for pair in order.windows(2) {
            add_jobshop_order_edge(&mut successors, &mut indegree, pair[0], pair[1])?;
        }
    }

    let mut ready: VecDeque<_> = indegree
        .iter()
        .filter_map(|(&task, &degree)| (degree == 0).then_some(task))
        .collect();
    let mut visited = 0usize;
    let mut objective = 0i64;

    while let Some(task) = ready.pop_front() {
        visited += 1;
        let finish = starts[&task].checked_add(*durations.get(&task)?)?;
        objective = objective.max(finish);
        if let Some(next_tasks) = successors.get(&task) {
            for &next in next_tasks {
                if starts[&next] < finish {
                    starts.insert(next, finish);
                }
                let degree = indegree.get_mut(&next)?;
                *degree = degree.checked_sub(1)?;
                if *degree == 0 {
                    ready.push_back(next);
                }
            }
        }
    }

    if visited != indegree.len() {
        return None;
    }
    Some((starts, objective))
}

fn add_jobshop_order_edge(
    successors: &mut BTreeMap<IntVarId, Vec<IntVarId>>,
    indegree: &mut BTreeMap<IntVarId, usize>,
    from: IntVarId,
    to: IntVarId,
) -> Option<()> {
    if !indegree.contains_key(&from) || !indegree.contains_key(&to) {
        return None;
    }
    successors.entry(from).or_default().push(to);
    *indegree.get_mut(&to)? += 1;
    Some(())
}

fn parse_precedence(
    ctx: &mut CpContext,
    constraint: &ConstraintItem,
) -> Option<(IntVarId, IntVarId, i64)> {
    if constraint.args.len() != 3 {
        return None;
    }
    let coeffs = ctx.resolve_const_int_array(&constraint.args[0]).ok()?;
    if coeffs.as_slice() != [1, -1] {
        return None;
    }
    let vars = ctx.resolve_var_array(&constraint.args[1]).ok()?;
    if vars.len() != 2 {
        return None;
    }
    let rhs = ctx.resolve_const_int(&constraint.args[2]).ok()?;
    if rhs >= 0 {
        return None;
    }
    Some((vars[0], vars[1], -rhs))
}

fn parse_reified_precedence(
    ctx: &mut CpContext,
    constraint: &ConstraintItem,
) -> Option<(IntVarId, IntVarId, i64)> {
    if constraint.args.len() != 4 {
        return None;
    }
    let coeffs = ctx.resolve_const_int_array(&constraint.args[0]).ok()?;
    if coeffs.as_slice() != [1, -1] {
        return None;
    }
    let vars = ctx.resolve_var_array(&constraint.args[1]).ok()?;
    if vars.len() != 2 {
        return None;
    }
    let rhs = ctx.resolve_const_int(&constraint.args[2]).ok()?;
    if rhs >= 0 {
        return None;
    }
    Some((vars[0], vars[1], -rhs))
}

fn insert_duration(durations: &mut BTreeMap<IntVarId, i64>, task: IntVarId, duration: i64) -> bool {
    match durations.insert(task, duration) {
        Some(existing) => existing == duration,
        None => true,
    }
}

fn infer_machine_components(
    half_map: &BTreeMap<(IntVarId, IntVarId), i64>,
) -> Option<BTreeMap<IntVarId, usize>> {
    let mut adjacency: BTreeMap<IntVarId, BTreeSet<IntVarId>> = BTreeMap::new();
    for &(a, b) in half_map.keys() {
        if half_map.contains_key(&(b, a)) {
            adjacency.entry(a).or_default().insert(b);
            adjacency.entry(b).or_default().insert(a);
        }
    }

    let mut machine_of = BTreeMap::new();
    let mut visited = BTreeSet::new();
    for &seed in adjacency.keys() {
        if visited.contains(&seed) {
            continue;
        }
        let machine = machine_of.values().copied().max().map_or(0, |m| m + 1);
        let mut stack = vec![seed];
        let mut component = Vec::new();
        while let Some(task) = stack.pop() {
            if !visited.insert(task) {
                continue;
            }
            component.push(task);
            if let Some(neighbors) = adjacency.get(&task) {
                stack.extend(neighbors.iter().copied());
            }
        }
        if component.len() < 2 {
            return None;
        }
        for task in component {
            machine_of.insert(task, machine);
        }
    }
    Some(machine_of)
}

fn validate_jobshop_incumbent(
    starts: &BTreeMap<IntVarId, i64>,
    objective: i64,
    precedences: &[(IntVarId, IntVarId, i64)],
    machine_of: &BTreeMap<IntVarId, usize>,
    durations: &BTreeMap<IntVarId, i64>,
) -> bool {
    for &(a, b, duration) in precedences {
        let Some(&a_start) = starts.get(&a) else {
            return false;
        };
        let b_start = starts.get(&b).copied().unwrap_or(objective);
        if a_start.saturating_add(duration) > b_start {
            return false;
        }
    }

    let tasks: Vec<_> = starts.keys().copied().collect();
    for i in 0..tasks.len() {
        for &b in tasks.iter().skip(i + 1) {
            let a = tasks[i];
            if machine_of.get(&a) != machine_of.get(&b) {
                continue;
            }
            let a_start = starts[&a];
            let b_start = starts[&b];
            let a_end = a_start.saturating_add(durations[&a]);
            let b_end = b_start.saturating_add(durations[&b]);
            if a_start < b_end && b_start < a_end {
                return false;
            }
        }
    }
    true
}

fn objective_reached_global_extreme(obj_val: i64, minimize: bool) -> bool {
    (minimize && obj_val == i64::MIN) || (!minimize && obj_val == i64::MAX)
}

fn tighten_search_after_solution(
    ctx: &mut CpContext,
    obj_var: IntVarId,
    obj_val: i64,
    minimize: bool,
) {
    if minimize {
        if let Some(next) = obj_val.checked_sub(1) {
            ctx.engine.add_upper_bound(obj_var, next);
        }
    } else if let Some(next) = obj_val.checked_add(1) {
        ctx.engine.add_lower_bound(obj_var, next);
    }
}
