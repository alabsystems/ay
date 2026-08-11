// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Global constraint encodings for FlatZinc-to-SMT translation

use ay_flatzinc_parser::ast::{ConstraintItem, Expr};

use crate::error::TranslateError;
use crate::globals_count;
use crate::globals_extra;
use crate::globals_regular;
use crate::translate::{ensure_quadratic_work, materialized_range_len, Context, SmtInt};

/// Translate a global FlatZinc constraint. Returns Ok(true) if handled.
pub(crate) fn translate_global(
    ctx: &mut Context,
    c: &ConstraintItem,
) -> Result<bool, TranslateError> {
    let Some(expected) = global_arity(&c.id) else {
        return Ok(false);
    };
    if c.args.len() != expected {
        return Err(TranslateError::WrongArgCount {
            name: c.id.clone(),
            expected,
            got: c.args.len(),
        });
    }

    match c.id.as_str() {
        "fzn_all_different_int" | "alldifferent" | "alldifferent_int" | "all_different_int" => {
            alldifferent(ctx, &c.args)?;
        }
        "fzn_table_int" | "table_int" => {
            table_int(ctx, &c.args)?;
        }
        "fzn_count_eq" | "count_eq" => {
            globals_count::count_eq(ctx, &c.args)?;
        }
        "fzn_count_neq" | "count_neq" => {
            globals_count::count_neq(ctx, &c.args)?;
        }
        "fzn_count_lt" | "count_lt" => {
            globals_count::count_lt(ctx, &c.args)?;
        }
        "fzn_count_gt" | "count_gt" => {
            globals_count::count_gt(ctx, &c.args)?;
        }
        "fzn_count_leq" | "count_leq" => {
            globals_count::count_leq(ctx, &c.args)?;
        }
        "fzn_count_geq" | "count_geq" => {
            globals_count::count_geq(ctx, &c.args)?;
        }
        "fzn_among" | "among" => {
            globals_count::among(ctx, &c.args)?;
        }
        "fzn_value_precede_int" | "value_precede_int" => {
            globals_extra::value_precede_int(ctx, &c.args)?;
        }
        "fzn_value_precede_chain_int" | "value_precede_chain_int" => {
            globals_extra::value_precede_chain_int(ctx, &c.args)?;
        }
        "fzn_circuit" | "circuit" => {
            circuit(ctx, &c.args)?;
        }
        "fzn_cumulative" | "cumulative" => {
            cumulative(ctx, &c.args)?;
        }
        "fzn_inverse" | "inverse" => {
            inverse(ctx, &c.args)?;
        }
        "fzn_diffn" | "diffn" => {
            diffn(ctx, &c.args)?;
        }
        "fzn_regular" | "regular" => {
            globals_regular::regular(ctx, &c.args)?;
        }
        "fzn_global_cardinality" | "global_cardinality" => {
            globals_extra::global_cardinality(ctx, &c.args, false)?;
        }
        "fzn_global_cardinality_closed" | "global_cardinality_closed" => {
            globals_extra::global_cardinality(ctx, &c.args, true)?;
        }
        "fzn_increasing_int" | "increasing_int" => {
            globals_extra::increasing_int(ctx, &c.args)?;
        }
        "fzn_decreasing_int" | "decreasing_int" => {
            globals_extra::decreasing_int(ctx, &c.args)?;
        }
        "fzn_member_int" | "member_int" => {
            globals_extra::member_int(ctx, &c.args)?;
        }
        "fzn_member_bool" | "member_bool" => {
            globals_extra::member_bool(ctx, &c.args)?;
        }
        "fzn_nvalue" | "nvalue" => {
            globals_extra::nvalue(ctx, &c.args)?;
        }
        "fzn_lex_less_int" | "lex_less_int" => {
            globals_extra::lex_compare_int(ctx, &c.args, true)?;
        }
        "fzn_lex_lesseq_int" | "lex_lesseq_int" => {
            globals_extra::lex_compare_int(ctx, &c.args, false)?;
        }
        "fzn_bin_packing_load" | "bin_packing_load" => {
            globals_extra::bin_packing_load(ctx, &c.args)?;
        }
        "fzn_subcircuit" | "subcircuit" => {
            globals_extra::subcircuit(ctx, &c.args)?;
        }
        "fzn_disjunctive" | "disjunctive" => {
            globals_extra::disjunctive(
                ctx,
                &c.args,
                globals_extra::DisjunctiveMode::ZeroDurationPermitted,
            )?;
        }
        "fzn_disjunctive_strict" | "disjunctive_strict" => {
            globals_extra::disjunctive(ctx, &c.args, globals_extra::DisjunctiveMode::Strict)?;
        }
        // `global_arity` recognizes exactly the aliases above. Keep this
        // defensive fallback non-panicking if the tables ever drift.
        _ => return Ok(false),
    }
    Ok(true)
}

fn global_arity(name: &str) -> Option<usize> {
    match name {
        "fzn_all_different_int"
        | "alldifferent"
        | "alldifferent_int"
        | "all_different_int"
        | "fzn_circuit"
        | "circuit"
        | "fzn_increasing_int"
        | "increasing_int"
        | "fzn_decreasing_int"
        | "decreasing_int"
        | "fzn_subcircuit"
        | "subcircuit" => Some(1),
        "fzn_table_int"
        | "table_int"
        | "fzn_inverse"
        | "inverse"
        | "fzn_value_precede_chain_int"
        | "value_precede_chain_int"
        | "fzn_member_int"
        | "member_int"
        | "fzn_member_bool"
        | "member_bool"
        | "fzn_nvalue"
        | "nvalue"
        | "fzn_lex_less_int"
        | "lex_less_int"
        | "fzn_lex_lesseq_int"
        | "lex_lesseq_int"
        | "fzn_disjunctive"
        | "disjunctive"
        | "fzn_disjunctive_strict"
        | "disjunctive_strict" => Some(2),
        "fzn_count_eq"
        | "count_eq"
        | "fzn_count_neq"
        | "count_neq"
        | "fzn_count_lt"
        | "count_lt"
        | "fzn_count_gt"
        | "count_gt"
        | "fzn_count_leq"
        | "count_leq"
        | "fzn_count_geq"
        | "count_geq"
        | "fzn_among"
        | "among"
        | "fzn_value_precede_int"
        | "value_precede_int"
        | "fzn_global_cardinality"
        | "global_cardinality"
        | "fzn_global_cardinality_closed"
        | "global_cardinality_closed"
        | "fzn_bin_packing_load"
        | "bin_packing_load" => Some(3),
        "fzn_cumulative" | "cumulative" | "fzn_diffn" | "diffn" => Some(4),
        "fzn_regular" | "regular" => Some(6),
        _ => None,
    }
}

/// Pairwise-inequality encoding: `∧_{i<j} (≠ x[i] x[j])`
///
/// O(n²) assertions. Sufficient for arrays up to ~50 elements.
fn alldifferent(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.is_empty() {
        return Ok(());
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    ensure_quadratic_work("all_different", vars.len(), vars.len(), 1)?;
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
/// The successor values use the array's declared index set.
///
/// Encoding:
/// 1. alldifferent(succ) — successor values form a permutation
/// 2. No self-loops: succ[i] ≠ i for all i
/// 3. MTZ subtour elimination, anchored at the first declared index.
fn circuit(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 1 {
        return Err(TranslateError::WrongArgCount {
            name: "circuit".into(),
            expected: 1,
            got: args.len(),
        });
    }
    let (lo, hi, vars) = ctx.expr_to_smt_indexed_array(&args[0])?;
    let n = vars.len();
    validate_indexed_array_cardinality("circuit", lo, hi, n)?;
    // Pairwise distinctness plus the edge/rank implications are both
    // quadratic. Two work items per matrix cell is a conservative bound.
    ensure_quadratic_work("circuit", n, n, 2)?;

    emit_index_range_guards(ctx, &vars, lo, hi);

    if n == 0 {
        return Ok(());
    }

    // A one-node Hamiltonian circuit is its self-loop. The general encoding
    // bans self-loops because that is only correct once there are two nodes.
    if n == 1 {
        ctx.emit_fmt(format_args!("(assert (= {} {}))", vars[0], SmtInt(lo)));
        return Ok(());
    }

    let aux_id = ctx.next_aux_id();

    // 1. All-different (pairwise)
    for i in 0..n {
        for j in (i + 1)..n {
            ctx.emit_fmt(format_args!("(assert (not (= {} {})))", vars[i], vars[j]));
        }
    }

    // 2. No self-loops.
    for (node, var) in (lo..=hi).zip(&vars) {
        ctx.emit_fmt(format_args!("(assert (not (= {} {})))", var, SmtInt(node)));
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

    // For each successor edge: if succ[i] targets a non-root node j, then
    // u[j] >= u[i] + 1. Auxiliary names use positions, while successor
    // values use the declared FlatZinc indices.
    for (i, var) in vars.iter().enumerate() {
        let u_i = if i == 0 {
            "1".to_string() // u[1] = 1 (start node)
        } else {
            format!("_circ{}_{}", aux_id, i + 1)
        };
        for j_idx in 1..n {
            let node_position = j_idx + 1;
            let node_value = lo + j_idx as i64;
            let u_j = format!("_circ{aux_id}_{node_position}");
            ctx.emit_fmt(format_args!(
                "(assert (=> (= {} {}) (>= {} (+ {} 1))))",
                var,
                SmtInt(node_value),
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
    // Each task pair creates one declaration and two implications; include
    // the per-event load assertion in the fourth work item.
    ensure_quadratic_work("cumulative", n, n, 4)?;

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
    let (f_lo, f_hi, f_vars) = ctx.expr_to_smt_indexed_array(&args[0])?;
    let (g_lo, g_hi, g_vars) = ctx.expr_to_smt_indexed_array(&args[1])?;
    validate_indexed_array_cardinality("inverse first array", f_lo, f_hi, f_vars.len())?;
    validate_indexed_array_cardinality("inverse second array", g_lo, g_hi, g_vars.len())?;
    if f_vars.len() != g_vars.len() {
        return Err(TranslateError::UnsupportedType(format!(
            "inverse: array cardinality mismatch ({} and {})",
            f_vars.len(),
            g_vars.len()
        )));
    }
    ensure_quadratic_work("inverse", f_vars.len(), g_vars.len(), 2)?;

    // f is indexed by the first range and contains indices into g; g is
    // indexed by the second range and contains indices into f.
    emit_index_range_guards(ctx, &f_vars, g_lo, g_hi);
    emit_index_range_guards(ctx, &g_vars, f_lo, f_hi);

    for (i_val, f_var) in (f_lo..=f_hi).zip(&f_vars) {
        for (j_val, g_var) in (g_lo..=g_hi).zip(&g_vars) {
            let i_val = SmtInt(i_val);
            let j_val = SmtInt(j_val);
            ctx.emit_fmt(format_args!(
                "(assert (=> (= {f_var} {j_val}) (= {g_var} {i_val})))"
            ));
            ctx.emit_fmt(format_args!(
                "(assert (=> (= {g_var} {i_val}) (= {f_var} {j_val})))"
            ));
        }
    }
    Ok(())
}

pub(crate) fn validate_indexed_array_cardinality(
    name: &str,
    lo: i64,
    hi: i64,
    actual: usize,
) -> Result<(), TranslateError> {
    let expected = materialized_range_len(lo, hi, name)?;
    if actual != expected {
        return Err(TranslateError::UnsupportedType(format!(
            "{name}: declared index range {lo}..{hi} has cardinality {expected}, but the array contains {actual} values"
        )));
    }
    Ok(())
}

pub(crate) fn emit_index_range_guards(ctx: &mut Context, vars: &[String], lo: i64, hi: i64) {
    for var in vars {
        if hi < lo {
            ctx.emit("(assert false)");
        } else {
            ctx.emit_fmt(format_args!(
                "(assert (and (>= {var} {}) (<= {var} {})))",
                SmtInt(lo),
                SmtInt(hi)
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
    ensure_quadratic_work("diffn", n, n, 1)?;

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
