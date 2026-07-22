// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Global constraint encodings for FlatZinc-to-SMT translation

use ay_flatzinc_parser::ast::{ConstraintItem, Expr};

use crate::error::TranslateError;
use crate::globals_count;
use crate::globals_extra;
use crate::globals_regular;
use crate::translate::{Context, SmtInt};

/// Translate a global FlatZinc constraint. Returns Ok(true) if handled.
pub(crate) fn translate_global(
    ctx: &mut Context,
    c: &ConstraintItem,
) -> Result<bool, TranslateError> {
    let handled = match c.id.as_str() {
        "fzn_all_different_int" | "alldifferent" | "all_different_int" => {
            alldifferent(ctx, &c.args)?;
            true
        }
        "fzn_table_int" | "table_int" => {
            table_int(ctx, &c.args)?;
            true
        }
        "fzn_count_eq" | "count_eq" => {
            globals_count::count_eq(ctx, &c.args)?;
            true
        }
        "fzn_count_neq" | "count_neq" => {
            globals_count::count_neq(ctx, &c.args)?;
            true
        }
        "fzn_count_lt" | "count_lt" => {
            globals_count::count_lt(ctx, &c.args)?;
            true
        }
        "fzn_count_gt" | "count_gt" => {
            globals_count::count_gt(ctx, &c.args)?;
            true
        }
        "fzn_count_leq" | "count_leq" => {
            globals_count::count_leq(ctx, &c.args)?;
            true
        }
        "fzn_count_geq" | "count_geq" => {
            globals_count::count_geq(ctx, &c.args)?;
            true
        }
        "fzn_among" | "among" => {
            globals_count::among(ctx, &c.args)?;
            true
        }
        "fzn_value_precede_int"
        | "value_precede_int"
        | "fzn_value_precede_chain_int"
        | "value_precede_chain_int" => {
            globals_extra::value_precede_int(ctx, &c.args)?;
            true
        }
        "fzn_circuit" | "circuit" => {
            circuit(ctx, &c.args)?;
            true
        }
        "fzn_cumulative" | "cumulative" => {
            cumulative(ctx, &c.args)?;
            true
        }
        "fzn_inverse" | "inverse" => {
            inverse(ctx, &c.args)?;
            true
        }
        "fzn_diffn" | "diffn" => {
            diffn(ctx, &c.args)?;
            true
        }
        "fzn_regular" | "regular" => {
            globals_regular::regular(ctx, &c.args)?;
            true
        }
        "fzn_global_cardinality" | "global_cardinality" => {
            globals_extra::global_cardinality(ctx, &c.args, false)?;
            true
        }
        "fzn_global_cardinality_closed" | "global_cardinality_closed" => {
            globals_extra::global_cardinality(ctx, &c.args, true)?;
            true
        }
        "fzn_increasing_int" | "increasing_int" => {
            globals_extra::increasing_int(ctx, &c.args)?;
            true
        }
        "fzn_decreasing_int" | "decreasing_int" => {
            globals_extra::decreasing_int(ctx, &c.args)?;
            true
        }
        "fzn_member_int" | "member_int" => {
            globals_extra::member_int(ctx, &c.args)?;
            true
        }
        "fzn_member_bool" | "member_bool" => {
            globals_extra::member_bool(ctx, &c.args)?;
            true
        }
        "fzn_nvalue" | "nvalue" => {
            globals_extra::nvalue(ctx, &c.args)?;
            true
        }
        "fzn_lex_less_int" | "lex_less_int" => {
            globals_extra::lex_compare_int(ctx, &c.args, true)?;
            true
        }
        "fzn_lex_lesseq_int" | "lex_lesseq_int" => {
            globals_extra::lex_compare_int(ctx, &c.args, false)?;
            true
        }
        "fzn_bin_packing_load" | "bin_packing_load" => {
            globals_extra::bin_packing_load(ctx, &c.args)?;
            true
        }
        "fzn_subcircuit" | "subcircuit" => {
            globals_extra::subcircuit(ctx, &c.args)?;
            true
        }
        "fzn_disjunctive" | "disjunctive" | "fzn_disjunctive_strict" | "disjunctive_strict" => {
            globals_extra::disjunctive(ctx, &c.args)?;
            true
        }
        _ => false,
    };
    Ok(handled)
}

/// Pairwise-inequality encoding: `∧_{i<j} (≠ x[i] x[j])`
///
/// O(n²) assertions. Sufficient for arrays up to ~50 elements.
fn alldifferent(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.is_empty() {
        return Ok(());
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            ctx.emit_fmt(format_args!("(assert (not (= {} {})))", vars[i], vars[j]));
        }
    }
    Ok(())
}

/// Table constraint: x[1..n] must match one of the given tuples.
///
/// args: [x_array, flat_tuples]
/// The flat_tuples array has length `arity * num_tuples` where arity = len(x).
/// Encoding: `∨_t (∧_i (= x[i] t[i]))`
fn table_int(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 2 {
        return Err(TranslateError::WrongArgCount {
            name: "table_int".into(),
            expected: 2,
            got: args.len(),
        });
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    let arity = vars.len();
    if arity == 0 {
        return Ok(());
    }

    let flat_vals = ctx.resolve_int_array(&args[1])?;
    if flat_vals.len() % arity != 0 {
        return Err(TranslateError::UnsupportedType(format!(
            "table_int: tuple array length {} not divisible by arity {}",
            flat_vals.len(),
            arity,
        )));
    }

    let num_tuples = flat_vals.len() / arity;
    if num_tuples == 0 {
        ctx.emit("(assert false)");
        return Ok(());
    }

    let mut disjuncts = Vec::with_capacity(num_tuples);
    for t in 0..num_tuples {
        let eqs: Vec<String> = (0..arity)
            .map(|i| format!("(= {} {})", vars[i], SmtInt(flat_vals[t * arity + i])))
            .collect();
        if eqs.len() == 1 {
            disjuncts.push(eqs[0].clone());
        } else {
            disjuncts.push(format!("(and {})", eqs.join(" ")));
        }
    }

    if disjuncts.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", disjuncts[0]));
    } else {
        ctx.emit_fmt(format_args!("(assert (or {}))", disjuncts.join(" ")));
    }
    Ok(())
}

/// Circuit constraint: successor array forms a single Hamiltonian circuit.
///
/// args: [succ_array] where succ[i] = j means node i connects to node j.
/// Uses 1-based indexing (FlatZinc convention).
///
/// Encoding:
/// 1. alldifferent(succ) — successor values form a permutation
/// 2. No self-loops: succ[i] ≠ i for all i
/// 3. MTZ subtour elimination with auxiliary order variables u[2..n]:
///    - 2 ≤ u[i] ≤ n for i ∈ {2..n}
///    - (succ[i] = j) ⇒ (u[j] ≥ u[i] + 1) for j ∈ {2..n}
///    - u[1] = 1 implicitly (used as constant in implications)
fn circuit(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.is_empty() {
        return Ok(());
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    let n = vars.len();
    if n <= 1 {
        return Ok(());
    }

    emit_one_based_index_range_guards(ctx, &vars, n);

    let aux_id = ctx.next_aux_id();

    // 1. All-different (pairwise)
    for i in 0..n {
        for j in (i + 1)..n {
            ctx.emit_fmt(format_args!("(assert (not (= {} {})))", vars[i], vars[j]));
        }
    }

    // 2. No self-loops: succ[i] != i (1-indexed)
    for (i, var) in vars.iter().enumerate() {
        ctx.emit_fmt(format_args!(
            "(assert (not (= {} {})))",
            var,
            SmtInt(i as i64 + 1)
        ));
    }

    // 3. MTZ subtour elimination
    // Declare auxiliary order variables for nodes 2..n
    for node in 2..=n {
        let u_name = format!("_circ{aux_id}_{node}");
        ctx.emit_fmt(format_args!("(declare-const {u_name} Int)"));
        ctx.emit_fmt(format_args!("(assert (>= {u_name} 2))"));
        ctx.emit_fmt(format_args!(
            "(assert (<= {} {}))",
            u_name,
            SmtInt(n as i64)
        ));
    }

    // For each successor edge: if succ[i] = j (j >= 2), then u[j] >= u[i] + 1
    for (i, var) in vars.iter().enumerate() {
        let u_i = if i == 0 {
            "1".to_string() // u[1] = 1 (start node)
        } else {
            format!("_circ{}_{}", aux_id, i + 1)
        };
        for j_idx in 1..n {
            // j_idx maps to node j_idx+1 (nodes 2..n)
            let node_j = j_idx + 1;
            let u_j = format!("_circ{aux_id}_{node_j}");
            ctx.emit_fmt(format_args!(
                "(assert (=> (= {} {}) (>= {} (+ {} 1))))",
                var,
                SmtInt(node_j as i64),
                u_j,
                u_i
            ));
        }
    }

    Ok(())
}

/// Cumulative constraint: tasks must not exceed resource capacity at any time.
///
/// args: [starts, durations, resources, capacity]
///
/// Uses an event-point encoding with auxiliary variables: for each task i,
/// the sum of resources of all tasks active at time s[i] must not exceed
/// capacity. Task j is active at time t if s[j] <= t < s[j] + d[j].
///
/// Auxiliary integer variables avoid ite-in-arithmetic patterns that ay
/// returns "unknown" for. Each load variable is constrained by implications:
///   active => load = r[j]; !active => load = 0
///
/// Sound because the resource profile only increases at task start events,
/// so checking all start times captures all violations. O(n²) variables and
/// assertions — polynomial and complete.
fn cumulative(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 4 {
        return Err(TranslateError::WrongArgCount {
            name: "cumulative".into(),
            expected: 4,
            got: args.len(),
        });
    }
    let starts = ctx.expr_to_smt_array(&args[0])?;
    let durations = ctx.expr_to_smt_array(&args[1])?;
    let resources = ctx.expr_to_smt_array(&args[2])?;
    let capacity = ctx.expr_to_smt(&args[3])?;
    let n = starts.len();

    if n != durations.len() || n != resources.len() {
        return Err(TranslateError::UnsupportedType(
            "cumulative: array length mismatch".into(),
        ));
    }

    let aux_id = ctx.next_aux_id();

    // Event-point encoding: at each task start time s[i], assert that the
    // total resource usage of all simultaneously active tasks <= capacity.
    for i in 0..n {
        let mut load_vars = Vec::with_capacity(n);

        for j in 0..n {
            let load = format!("_cum{aux_id}_{i}_{j}");
            ctx.emit_fmt(format_args!("(declare-const {load} Int)"));

            // Task j is active at time s[i] iff s[j] <= s[i] < s[j] + d[j]
            let active = format!(
                "(and (<= {} {}) (< {} (+ {} {})))",
                starts[j], starts[i], starts[i], starts[j], durations[j],
            );

            // active => load = r[j]; !active => load = 0
            ctx.emit_fmt(format_args!(
                "(assert (=> {active} (= {load} {})))",
                resources[j]
            ));
            ctx.emit_fmt(format_args!("(assert (=> (not {active}) (= {load} 0)))"));

            load_vars.push(load);
        }

        // Sum of loads at this event point must not exceed capacity
        let sum = if load_vars.len() == 1 {
            load_vars[0].clone()
        } else {
            format!("(+ {})", load_vars.join(" "))
        };
        ctx.emit_fmt(format_args!("(assert (<= {sum} {capacity}))"));
    }

    Ok(())
}

/// Inverse constraint: f and g are inverse permutations.
///
/// args: [f_array, g_array]
/// Encoding: (f[i] = j) ⇔ (g[j] = i) for all i, j.
/// Implemented as O(n·m) implications in both directions.
fn inverse(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 2 {
        return Err(TranslateError::WrongArgCount {
            name: "inverse".into(),
            expected: 2,
            got: args.len(),
        });
    }
    let f_vars = ctx.expr_to_smt_array(&args[0])?;
    let g_vars = ctx.expr_to_smt_array(&args[1])?;

    emit_one_based_index_range_guards(ctx, &f_vars, g_vars.len());
    emit_one_based_index_range_guards(ctx, &g_vars, f_vars.len());

    // For each (i, j): (f[i] = j+1) => (g[j] = i+1) and vice versa
    for (i_idx, f_var) in f_vars.iter().enumerate() {
        for (j_idx, g_var) in g_vars.iter().enumerate() {
            let i_val = SmtInt(i_idx as i64 + 1);
            let j_val = SmtInt(j_idx as i64 + 1);
            // Forward: f[i+1] = j+1 => g[j+1] = i+1
            ctx.emit_fmt(format_args!(
                "(assert (=> (= {f_var} {j_val}) (= {g_var} {i_val})))"
            ));
            // Backward: g[j+1] = i+1 => f[i+1] = j+1
            ctx.emit_fmt(format_args!(
                "(assert (=> (= {g_var} {i_val}) (= {f_var} {j_val})))"
            ));
        }
    }
    Ok(())
}

fn emit_one_based_index_range_guards(ctx: &mut Context, vars: &[String], upper: usize) {
    for var in vars {
        if upper == 0 {
            ctx.emit("(assert false)");
        } else {
            let upper = SmtInt(upper as i64);
            ctx.emit_fmt(format_args!(
                "(assert (and (>= {var} 1) (<= {var} {upper})))"
            ));
        }
    }
}

/// Non-overlapping rectangles constraint.
///
/// args: [x_array, y_array, dx_array, dy_array]
/// Encoding: for each pair (i, j), at least one separation axis:
///   x[i]+dx[i] ≤ x[j] ∨ x[j]+dx[j] ≤ x[i] ∨
///   y[i]+dy[i] ≤ y[j] ∨ y[j]+dy[j] ≤ y[i]
fn diffn(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 4 {
        return Err(TranslateError::WrongArgCount {
            name: "diffn".into(),
            expected: 4,
            got: args.len(),
        });
    }
    let xs = ctx.expr_to_smt_array(&args[0])?;
    let ys = ctx.expr_to_smt_array(&args[1])?;
    let dxs = ctx.expr_to_smt_array(&args[2])?;
    let dys = ctx.expr_to_smt_array(&args[3])?;
    let n = xs.len();

    if n != ys.len() || n != dxs.len() || n != dys.len() {
        return Err(TranslateError::UnsupportedType(
            "diffn: array length mismatch".into(),
        ));
    }

    for i in 0..n {
        for j in (i + 1)..n {
            ctx.emit_fmt(format_args!(
                "(assert (or (<= (+ {} {}) {}) (<= (+ {} {}) {}) \
                 (<= (+ {} {}) {}) (<= (+ {} {}) {})))",
                xs[i],
                dxs[i],
                xs[j], // x[i]+dx[i] <= x[j]
                xs[j],
                dxs[j],
                xs[i], // x[j]+dx[j] <= x[i]
                ys[i],
                dys[i],
                ys[j], // y[i]+dy[i] <= y[j]
                ys[j],
                dys[j],
                ys[i], // y[j]+dy[j] <= y[i]
            ));
        }
    }
    Ok(())
}
