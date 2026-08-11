// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Additional global constraint encodings for FlatZinc-to-SMT translation.
// Split from globals.rs for file-size compliance.

use ay_flatzinc_parser::ast::Expr;

use crate::error::TranslateError;
use crate::globals::{emit_index_range_guards, validate_indexed_array_cardinality};
use crate::translate::{ensure_quadratic_work, Context, SmtInt};

/// Global cardinality constraint: count occurrences of each value in x.
///
/// args: [x_array, cover_values, counts]
/// For each cover_values[i], counts[i] = |{j : x[j] = cover_values[i]}|.
/// When `closed` is true, x values must be in the cover set.
pub(crate) fn global_cardinality(
    ctx: &mut Context,
    args: &[Expr],
    closed: bool,
) -> Result<(), TranslateError> {
    if args.len() != 3 {
        return Err(TranslateError::WrongArgCount {
            name: "global_cardinality".into(),
            expected: 3,
            got: args.len(),
        });
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    let cover = ctx.resolve_int_array(&args[1])?;
    let counts = ctx.expr_to_smt_array(&args[2])?;

    if cover.len() != counts.len() {
        return Err(TranslateError::UnsupportedType(
            "global_cardinality: cover and counts length mismatch".into(),
        ));
    }
    ensure_quadratic_work(
        "global_cardinality",
        cover.len(),
        vars.len(),
        1 + usize::from(closed),
    )?;

    // For each value v in cover, count = sum of (ite (= x[j] v) 1 0) for all j
    for (k, &val) in cover.iter().enumerate() {
        let terms: Vec<String> = vars
            .iter()
            .map(|v| format!("(ite (= {} {}) 1 0)", v, SmtInt(val)))
            .collect();
        let sum = if terms.is_empty() {
            "0".to_string()
        } else if terms.len() == 1 {
            terms[0].clone()
        } else {
            format!("(+ {})", terms.join(" "))
        };
        ctx.emit_fmt(format_args!("(assert (= {} {}))", counts[k], sum));
    }

    // Closed: all x values must be in the cover set
    if closed {
        for var in &vars {
            let disj: Vec<String> = cover
                .iter()
                .map(|&val| format!("(= {} {})", var, SmtInt(val)))
                .collect();
            if disj.is_empty() {
                ctx.emit("(assert false)");
            } else if disj.len() == 1 {
                ctx.emit_fmt(format_args!("(assert {})", disj[0]));
            } else {
                ctx.emit_fmt(format_args!("(assert (or {}))", disj.join(" ")));
            }
        }
    }

    Ok(())
}

/// Increasing constraint: array elements are in non-decreasing order.
///
/// args: [x_array]
/// Encoding: x[i] <= x[i+1] for all consecutive pairs.
pub(crate) fn increasing_int(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.is_empty() {
        return Ok(());
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    for i in 0..vars.len().saturating_sub(1) {
        ctx.emit_fmt(format_args!("(assert (<= {} {}))", vars[i], vars[i + 1]));
    }
    Ok(())
}

/// Decreasing constraint: array elements are in non-increasing order.
///
/// args: [x_array]
/// Encoding: x[i] >= x[i+1] for all consecutive pairs.
pub(crate) fn decreasing_int(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.is_empty() {
        return Ok(());
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    for i in 0..vars.len().saturating_sub(1) {
        ctx.emit_fmt(format_args!("(assert (>= {} {}))", vars[i], vars[i + 1]));
    }
    Ok(())
}

/// Member constraint: value y exists in array x.
///
/// args: [x_array, y]
/// Encoding: (or (= x[0] y) (= x[1] y) ... (= x[n-1] y))
pub(crate) fn member_int(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 2 {
        return Err(TranslateError::WrongArgCount {
            name: "member_int".into(),
            expected: 2,
            got: args.len(),
        });
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    let val = ctx.expr_to_smt(&args[1])?;

    if vars.is_empty() {
        ctx.emit("(assert false)");
        return Ok(());
    }

    let disj: Vec<String> = vars.iter().map(|v| format!("(= {v} {val})")).collect();
    if disj.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", disj[0]));
    } else {
        ctx.emit_fmt(format_args!("(assert (or {}))", disj.join(" ")));
    }
    Ok(())
}

/// Boolean member constraint: value y exists in boolean array x.
///
/// args: [x_array, y]
pub(crate) fn member_bool(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    member_int(ctx, args)
}

/// Nvalue constraint: the number of distinct values in x equals n.
///
/// args: [n, x_array]
/// Encoding: introduce a Boolean indicator for each variable: "is this the
/// first occurrence of its value?" b[i] = (x[i] != x[j] for all j < i).
/// Then n = sum of indicators.
pub(crate) fn nvalue(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 2 {
        return Err(TranslateError::WrongArgCount {
            name: "nvalue".into(),
            expected: 2,
            got: args.len(),
        });
    }
    let n_expr = ctx.expr_to_smt(&args[0])?;
    let vars = ctx.expr_to_smt_array(&args[1])?;
    ensure_quadratic_work("nvalue", vars.len(), vars.len(), 1)?;

    if vars.is_empty() {
        ctx.emit_fmt(format_args!("(assert (= {n_expr} 0))"));
        return Ok(());
    }

    let aux_id = ctx.next_aux_id();

    // Introduce a Boolean indicator for each variable: "is this the first
    // occurrence of its value?"
    let mut indicator_names = Vec::with_capacity(vars.len());
    for i in 0..vars.len() {
        let ind = format!("_nv{aux_id}_{i}");
        ctx.emit_fmt(format_args!("(declare-const {ind} Bool)"));

        if i == 0 {
            // First element is always a "new" value
            ctx.emit_fmt(format_args!("(assert {ind})"));
        } else {
            // b[i] is true iff x[i] differs from all x[0..i]
            let all_diff: Vec<String> = (0..i)
                .map(|j| format!("(not (= {} {}))", vars[i], vars[j]))
                .collect();
            let cond = if all_diff.len() == 1 {
                all_diff[0].clone()
            } else {
                format!("(and {})", all_diff.join(" "))
            };
            ctx.emit_fmt(format_args!("(assert (= {ind} {cond}))"));
        }
        indicator_names.push(ind);
    }

    // n = sum of indicators
    let terms: Vec<String> = indicator_names
        .iter()
        .map(|ind| format!("(ite {ind} 1 0)"))
        .collect();
    let sum = if terms.len() == 1 {
        terms[0].clone()
    } else {
        format!("(+ {})", terms.join(" "))
    };
    ctx.emit_fmt(format_args!("(assert (= {n_expr} {sum}))"));

    Ok(())
}

/// Lexicographic comparison of two integer arrays.
///
/// args: [x_array, y_array]
/// `strict`: true for lex_less (strict), false for lex_lesseq (non-strict).
///
/// Encoding uses a chain of position comparisons:
///   lex_less: lt[0] or (eq[0] and lt[1]) or (eq[0] and eq[1] and lt[2]) ...
///   lex_lesseq: lex_less or all-equal
/// If the common prefix is equal, the shorter array is lexicographically less.
pub(crate) fn lex_compare_int(
    ctx: &mut Context,
    args: &[Expr],
    strict: bool,
) -> Result<(), TranslateError> {
    if args.len() != 2 {
        return Err(TranslateError::WrongArgCount {
            name: if strict {
                "lex_less_int"
            } else {
                "lex_lesseq_int"
            }
            .into(),
            expected: 2,
            got: args.len(),
        });
    }
    let xs = ctx.expr_to_smt_array(&args[0])?;
    let ys = ctx.expr_to_smt_array(&args[1])?;
    let n = xs.len().min(ys.len());
    ensure_quadratic_work("lex comparison", n, n, 1)?;

    // Build disjunction: lt[0], (eq[0] & lt[1]), (eq[0] & eq[1] & lt[2]), ...
    let mut disjuncts = Vec::with_capacity(n + 1);
    for i in 0..n {
        let lt_i = format!("(< {} {})", xs[i], ys[i]);
        if i == 0 {
            disjuncts.push(lt_i);
        } else {
            let eq_prefix: Vec<String> =
                (0..i).map(|j| format!("(= {} {})", xs[j], ys[j])).collect();
            let mut parts = eq_prefix;
            parts.push(lt_i);
            disjuncts.push(format!("(and {})", parts.join(" ")));
        }
    }

    // An equal common prefix satisfies the comparison exactly when the lhs is
    // shorter, or when both lengths match and the comparison is non-strict.
    if xs.len() < ys.len() || (!strict && xs.len() == ys.len()) {
        let all_eq: Vec<String> = (0..n).map(|j| format!("(= {} {})", xs[j], ys[j])).collect();
        if all_eq.is_empty() {
            disjuncts.push("true".to_string());
        } else if all_eq.len() == 1 {
            disjuncts.push(all_eq[0].clone());
        } else {
            disjuncts.push(format!("(and {})", all_eq.join(" ")));
        }
    }

    if disjuncts.is_empty() {
        ctx.emit("(assert false)");
    } else if disjuncts.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", disjuncts[0]));
    } else {
        ctx.emit_fmt(format_args!("(assert (or {}))", disjuncts.join(" ")));
    }

    Ok(())
}

/// Bin packing load constraint: load[b] = sum of sizes of items assigned to bin b.
///
/// args: [load_array, bin_array, size_array]
/// For each bin b: load[b] = sum_{i : bin[i] = b} size[i]
pub(crate) fn bin_packing_load(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 3 {
        return Err(TranslateError::WrongArgCount {
            name: "bin_packing_load".into(),
            expected: 3,
            got: args.len(),
        });
    }
    let (load_lo, load_hi, loads) = ctx.expr_to_smt_indexed_array(&args[0])?;
    let bins = ctx.expr_to_smt_array(&args[1])?;
    let sizes = ctx.resolve_int_array(&args[2])?;

    validate_indexed_array_cardinality(
        "bin_packing_load load array",
        load_lo,
        load_hi,
        loads.len(),
    )?;

    if bins.len() != sizes.len() {
        return Err(TranslateError::UnsupportedType(
            "bin_packing_load: bin and size array length mismatch".into(),
        ));
    }
    ensure_quadratic_work("bin_packing_load", loads.len(), bins.len(), 1)?;

    // Every item must be assigned to an index represented in `load`.
    // Without these guards, an out-of-range bin value contributes to no load.
    emit_index_range_guards(ctx, &bins, load_lo, load_hi);

    for (bin_idx, load_var) in (load_lo..=load_hi).zip(&loads) {
        let bin_idx = SmtInt(bin_idx);
        let terms: Vec<String> = bins
            .iter()
            .zip(sizes.iter())
            .map(|(bin_var, &size)| format!("(ite (= {} {}) {} 0)", bin_var, bin_idx, SmtInt(size)))
            .collect();
        let sum = if terms.is_empty() {
            "0".to_string()
        } else if terms.len() == 1 {
            terms[0].clone()
        } else {
            format!("(+ {})", terms.join(" "))
        };
        ctx.emit_fmt(format_args!("(assert (= {load_var} {sum}))"));
    }

    Ok(())
}

/// Subcircuit constraint: non-self-loop nodes form one cycle; remaining nodes
/// are self-loops.
///
/// args: [succ_array]
/// Unlike `circuit`, self-loops are allowed and indicate unused nodes.
/// Encoding:
/// 1. alldifferent(succ)
/// 2. The smallest active node is selected as the cycle root.
/// 3. Rank constraints exclude any second active cycle.
pub(crate) fn subcircuit(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 1 {
        return Err(TranslateError::WrongArgCount {
            name: "subcircuit".into(),
            expected: 1,
            got: args.len(),
        });
    }
    let (lo, hi, vars) = ctx.expr_to_smt_indexed_array(&args[0])?;
    let n = vars.len();
    validate_indexed_array_cardinality("subcircuit", lo, hi, n)?;
    // Pairwise distinctness, prefix-root construction, and edge/rank
    // implications together stay below two matrix-sized work units.
    ensure_quadratic_work("subcircuit", n, n, 2)?;
    emit_index_range_guards(ctx, &vars, lo, hi);

    if n == 0 {
        return Ok(());
    }

    let aux_id = ctx.next_aux_id();
    let nodes: Vec<i64> = (lo..=hi).collect();

    // 1. All-different (pairwise)
    for i in 0..n {
        for j in (i + 1)..n {
            ctx.emit_fmt(format_args!("(assert (not (= {} {})))", vars[i], vars[j]));
        }
    }

    // 2. Active node tracking. Auxiliary symbol suffixes are ordinal so
    // negative FlatZinc indices never leak into SMT symbol names.
    let mut active_names = Vec::with_capacity(n);
    for (ordinal, (node, var)) in nodes.iter().zip(&vars).enumerate() {
        let active = format!("_sc_act{aux_id}_{ordinal}");
        ctx.emit_fmt(format_args!("(declare-const {active} Bool)"));
        ctx.emit_fmt(format_args!(
            "(assert (= {active} (not (= {} {}))))",
            var,
            SmtInt(*node)
        ));
        active_names.push(active);
    }

    // Select the smallest active node as root. This permits a cycle that does
    // not contain the first array index while choosing exactly one root when
    // at least one node is active.
    let mut root_names = Vec::with_capacity(n);
    for ordinal in 0..n {
        let root = format!("_sc_root{aux_id}_{ordinal}");
        ctx.emit_fmt(format_args!("(declare-const {root} Bool)"));
        let root_definition = if ordinal == 0 {
            active_names[0].clone()
        } else {
            let mut terms = Vec::with_capacity(ordinal + 1);
            terms.push(active_names[ordinal].clone());
            terms.extend(
                active_names[..ordinal]
                    .iter()
                    .map(|active| format!("(not {active})")),
            );
            format!("(and {})", terms.join(" "))
        };
        ctx.emit_fmt(format_args!("(assert (= {root} {root_definition}))"));
        root_names.push(root);
    }

    let rank_upper = i64::try_from(n - 1)
        .map_err(|_| TranslateError::UnsupportedType("subcircuit array is too large".into()))?;
    let mut rank_names = Vec::with_capacity(n);
    for ordinal in 0..n {
        let rank = format!("_sc_ord{aux_id}_{ordinal}");
        ctx.emit_fmt(format_args!("(declare-const {rank} Int)"));
        ctx.emit_fmt(format_args!("(assert (>= {rank} 0))"));
        ctx.emit_fmt(format_args!("(assert (<= {rank} {}))", SmtInt(rank_upper)));
        ctx.emit_fmt(format_args!(
            "(assert (=> {} (= {rank} 0)))",
            root_names[ordinal]
        ));
        rank_names.push(rank);
    }

    // Ranks increase along every active edge except the edge that closes the
    // selected root's cycle. A second cycle would require a strict increase
    // all the way around and is therefore impossible.
    for (source, var) in vars.iter().enumerate() {
        for (target, node) in nodes.iter().enumerate() {
            ctx.emit_fmt(format_args!(
                "(assert (=> (and {} (= {} {}) (not {})) (= {} (+ {} 1))))",
                active_names[source],
                var,
                SmtInt(*node),
                root_names[target],
                rank_names[target],
                rank_names[source],
            ));
        }
    }

    Ok(())
}

#[derive(Clone, Copy)]
pub(crate) enum DisjunctiveMode {
    /// Ordinary MiniZinc semantics: zero-duration tasks consume no resource.
    ZeroDurationPermitted,
    /// Strict semantics: even a zero-duration task must satisfy the ordering.
    Strict,
}

/// Disjunctive constraint: non-overlapping tasks on a single resource.
///
/// args: [starts, durations]
/// Encoding: for each pair (i, j), either task i ends before j starts or
/// task j ends before i starts: s[i]+d[i] <= s[j] or s[j]+d[j] <= s[i].
pub(crate) fn disjunctive(
    ctx: &mut Context,
    args: &[Expr],
    mode: DisjunctiveMode,
) -> Result<(), TranslateError> {
    if args.len() != 2 {
        return Err(TranslateError::WrongArgCount {
            name: "disjunctive".into(),
            expected: 2,
            got: args.len(),
        });
    }
    let starts = ctx.expr_to_smt_array(&args[0])?;
    let durations = ctx.expr_to_smt_array(&args[1])?;
    let n = starts.len();

    if n != durations.len() {
        return Err(TranslateError::UnsupportedType(
            "disjunctive: array length mismatch".into(),
        ));
    }
    ensure_quadratic_work("disjunctive", n, n, 1)?;

    for i in 0..n {
        for j in (i + 1)..n {
            match mode {
                DisjunctiveMode::ZeroDurationPermitted => ctx.emit_fmt(format_args!(
                    "(assert (or (= {} 0) (= {} 0) (<= (+ {} {}) {}) (<= (+ {} {}) {})))",
                    durations[i],
                    durations[j],
                    starts[i],
                    durations[i],
                    starts[j],
                    starts[j],
                    durations[j],
                    starts[i],
                )),
                DisjunctiveMode::Strict => ctx.emit_fmt(format_args!(
                    "(assert (or (<= (+ {} {}) {}) (<= (+ {} {}) {})))",
                    starts[i], durations[i], starts[j], starts[j], durations[j], starts[i],
                )),
            }
        }
    }
    Ok(())
}

/// Value-precede constraint for integers: if value t appears in x,
/// then value s must appear before the first occurrence of t.
///
/// args: [s, t, x_array]
/// Encoding: introduce prefix Booleans `seen_s[i]`. At every position i where
/// x[i] = t, require that s was seen at a strictly earlier position.
pub(crate) fn value_precede_int(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 3 {
        return Err(TranslateError::WrongArgCount {
            name: "value_precede_int".into(),
            expected: 3,
            got: args.len(),
        });
    }
    let s_val = ctx.expr_to_smt(&args[0])?;
    let t_val = ctx.expr_to_smt(&args[1])?;
    let vars = ctx.expr_to_smt_array(&args[2])?;

    emit_value_precede(ctx, &s_val, &t_val, &vars);
    Ok(())
}

/// Value-precede chain: each adjacent value in `cover` must precede the next
/// one in the sequence whenever the latter occurs.
///
/// args: [cover_array, x_array]
pub(crate) fn value_precede_chain_int(
    ctx: &mut Context,
    args: &[Expr],
) -> Result<(), TranslateError> {
    if args.len() != 2 {
        return Err(TranslateError::WrongArgCount {
            name: "value_precede_chain_int".into(),
            expected: 2,
            got: args.len(),
        });
    }
    let cover = ctx.resolve_int_array(&args[0])?;
    let vars = ctx.expr_to_smt_array(&args[1])?;
    ensure_quadratic_work(
        "value_precede_chain_int",
        cover.len().saturating_sub(1),
        vars.len(),
        2,
    )?;

    for pair in cover.windows(2) {
        emit_value_precede(
            ctx,
            &SmtInt(pair[0]).to_string(),
            &SmtInt(pair[1]).to_string(),
            &vars,
        );
    }
    Ok(())
}

fn emit_value_precede(ctx: &mut Context, s_val: &str, t_val: &str, vars: &[String]) {
    if vars.is_empty() {
        return;
    }

    let aux_id = ctx.next_aux_id();

    // Track whether s has been seen at or before position i, but test t
    // against the previous prefix so precedence is strict in the index.
    for (i, var) in vars.iter().enumerate() {
        let seen_s = format!("_vp_s{aux_id}_{i}");
        ctx.emit_fmt(format_args!("(declare-const {seen_s} Bool)"));

        if i == 0 {
            ctx.emit_fmt(format_args!("(assert (not (= {var} {t_val})))"));
            ctx.emit_fmt(format_args!("(assert (= {seen_s} (= {var} {s_val})))"));
        } else {
            let prev = format!("_vp_s{aux_id}_{}", i - 1);
            ctx.emit_fmt(format_args!("(assert (=> (= {var} {t_val}) {prev}))"));
            ctx.emit_fmt(format_args!(
                "(assert (= {seen_s} (or {prev} (= {var} {s_val}))))"
            ));
        }
    }
}
