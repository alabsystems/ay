// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Regular (DFA) global constraint encoding for FlatZinc-to-SMT translation

use ay_core::kani_compat::DetHashMap as HashMap;

use ay_flatzinc_parser::ast::Expr;

use crate::error::TranslateError;
use crate::translate::{Context, SmtInt, MAX_MATERIALIZED_ITEMS};

/// Regular constraint: sequence x[1..n] must be accepted by a DFA.
///
/// args: [x_array, Q, S, d_flat, q0, F_set]
/// - x: array of variables (1-indexed values from input alphabet 1..S)
/// - Q: number of states
/// - S: size of input alphabet
/// - d_flat: flat transition table, length Q*S, d[q][s] = d_flat[(q-1)*S + (s-1)]
/// - q0: initial state (1-based)
/// - F: set of accepting states
///
/// Encoding: layered Boolean variables b[t][q] = "in state q at step t".
pub(crate) fn regular(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 6 {
        return Err(TranslateError::WrongArgCount {
            name: "regular".into(),
            expected: 6,
            got: args.len(),
        });
    }

    let x_vars = ctx.expr_to_smt_array(&args[0])?;
    let n = x_vars.len();

    let q_count = positive_count(ctx.resolve_int(&args[1])?, "state count")?;
    let s_count = positive_count(ctx.resolve_int(&args[2])?, "alphabet size")?;
    let d_flat = ctx.resolve_int_array(&args[3])?;
    let q0 = positive_count(ctx.resolve_int(&args[4])?, "initial state")?;
    let f_set = ctx.resolve_set(&args[5])?;

    let transition_count = q_count.checked_mul(s_count).ok_or_else(|| {
        TranslateError::UnsupportedType(
            "regular: Q*S overflows the platform's index size".to_string(),
        )
    })?;
    if d_flat.len() != transition_count {
        return Err(TranslateError::UnsupportedType(format!(
            "regular: transition table length {} != Q*S = {}*{} = {}",
            d_flat.len(),
            q_count,
            s_count,
            transition_count
        )));
    }
    if q0 > q_count {
        return Err(TranslateError::UnsupportedType(format!(
            "regular: initial state {q0} is outside 1..={q_count}"
        )));
    }
    for &destination in &d_flat {
        if destination < 0
            || usize::try_from(destination)
                .ok()
                .is_none_or(|q| q > q_count)
        {
            return Err(TranslateError::UnsupportedType(format!(
                "regular: transition destination {destination} is outside 0..={q_count}"
            )));
        }
    }
    for &accepting in &f_set {
        if accepting < 1 || usize::try_from(accepting).ok().is_none_or(|q| q > q_count) {
            return Err(TranslateError::UnsupportedType(format!(
                "regular: accepting state {accepting} is outside 1..={q_count}"
            )));
        }
    }
    let non_sink_transitions = d_flat
        .iter()
        .filter(|&&destination| destination != 0)
        .count();
    validate_emission_work(n, q_count, non_sink_transitions)?;

    let aux_id = ctx.next_aux_id();

    // Declare layered Booleans and set initial state
    regular_init(ctx, aux_id, n, q_count, q0);

    // Encode DFA transitions
    regular_transitions(ctx, aux_id, &x_vars, q_count, s_count, &d_flat);

    // Encode accepting condition
    regular_accept(ctx, aux_id, n, &f_set);

    Ok(())
}

fn positive_count(value: i64, label: &str) -> Result<usize, TranslateError> {
    if value <= 0 {
        return Err(TranslateError::UnsupportedType(format!(
            "regular: {label} must be positive, got {value}"
        )));
    }
    usize::try_from(value).map_err(|_| {
        TranslateError::UnsupportedType(format!(
            "regular: {label} {value} does not fit the platform's index size"
        ))
    })
}

/// Bound the work that `regular_init` and `regular_transitions` materialize.
/// Counting only layered state variables misses both the retained reverse
/// transition table and the `n * Q * S` family of emitted reaching terms;
/// transitions to state zero are sinks and require neither.
fn validate_emission_work(
    n: usize,
    q_count: usize,
    non_sink_transitions: usize,
) -> Result<(), TranslateError> {
    let layer_count = n
        .checked_add(1)
        .and_then(|layers| layers.checked_mul(q_count))
        .ok_or_else(|| {
            TranslateError::UnsupportedType(
                "regular: layered automaton size overflows the platform's index size".to_string(),
            )
        })?;
    let transition_assertions = n.checked_mul(q_count).ok_or_else(|| {
        TranslateError::UnsupportedType(
            "regular: transition assertion count overflows the platform's index size".to_string(),
        )
    })?;
    let reaching_terms = n.checked_mul(non_sink_transitions).ok_or_else(|| {
        TranslateError::UnsupportedType(
            "regular: reaching-term count overflows the platform's index size".to_string(),
        )
    })?;
    // An empty sequence never consults the transition relation, so
    // `regular_transitions` returns before constructing its reverse table.
    let reverse_entries = if n == 0 { 0 } else { non_sink_transitions };
    let work = layer_count
        .checked_add(q_count)
        .and_then(|work| work.checked_add(transition_assertions))
        .and_then(|work| work.checked_add(reaching_terms))
        .and_then(|work| work.checked_add(reverse_entries))
        .and_then(|work| work.checked_add(1))
        .ok_or_else(|| {
            TranslateError::UnsupportedType(
                "regular: total emission work overflows the platform's index size".to_string(),
            )
        })?;
    if work > MAX_MATERIALIZED_ITEMS {
        return Err(TranslateError::UnsupportedType(format!(
            "regular: encoding emits {work} declarations, assertions, and transition terms, exceeding the maximum supported {MAX_MATERIALIZED_ITEMS}"
        )));
    }
    Ok(())
}

/// Declare layered Boolean variables and set initial state for regular constraint.
fn regular_init(ctx: &mut Context, aux_id: usize, n: usize, q_count: usize, q0: usize) {
    for t in 0..=n {
        for q in 1..=q_count {
            let name = format!("_reg{aux_id}_{t}_{q}");
            ctx.emit_fmt(format_args!("(declare-const {name} Bool)"));
        }
    }
    // b[0][q0] = true, b[0][q] = false for q != q0
    for q in 1..=q_count {
        let name = format!("_reg{aux_id}_0_{q}");
        if q == q0 {
            ctx.emit_fmt(format_args!("(assert {name})"));
        } else {
            ctx.emit_fmt(format_args!("(assert (not {name}))"));
        }
    }
}

/// Encode DFA transitions: b[t+1][q'] = ∨_{q,s} (b[t][q] ∧ x[t+1]=s ∧ d[q][s]=q').
///
/// Uses a pre-computed reverse transition table (q_target → [(q_src, s)]) to avoid
/// the O(n × Q² × S) inner scan. Complexity is O(Q × S) for table construction
/// plus O(n × Q × avg_fan_in) for emission. See #326.
fn regular_transitions(
    ctx: &mut Context,
    aux_id: usize,
    x_vars: &[String],
    q_count: usize,
    s_count: usize,
    d_flat: &[i64],
) {
    if x_vars.is_empty() {
        return;
    }

    // Pre-compute reverse transition table: q_target -> [(q_src, s)]
    let mut reverse: HashMap<usize, Vec<(usize, usize)>> = HashMap::default();
    for q_src in 1..=q_count {
        for s in 1..=s_count {
            let dest = d_flat[(q_src - 1) * s_count + (s - 1)] as usize;
            if dest != 0 {
                reverse.entry(dest).or_default().push((q_src, s));
            }
        }
    }

    for (t, x_var) in x_vars.iter().enumerate() {
        for q_target in 1..=q_count {
            let b_next = format!("_reg{aux_id}_{}_{}", t + 1, q_target);
            let reaching: Vec<String> = reverse
                .get(&q_target)
                .map(|sources| {
                    sources
                        .iter()
                        .map(|(q_src, s)| {
                            let b_cur = format!("_reg{aux_id}_{t}_{q_src}");
                            format!("(and {b_cur} (= {} {}))", x_var, SmtInt(*s as i64))
                        })
                        .collect()
                })
                .unwrap_or_default();

            if reaching.is_empty() {
                ctx.emit_fmt(format_args!("(assert (not {b_next}))"));
            } else if reaching.len() == 1 {
                ctx.emit_fmt(format_args!("(assert (= {b_next} {}))", reaching[0]));
            } else {
                ctx.emit_fmt(format_args!(
                    "(assert (= {b_next} (or {})))",
                    reaching.join(" ")
                ));
            }
        }
    }
}

/// Encode DFA accepting condition: ∨_{q ∈ F} b[n][q].
fn regular_accept(ctx: &mut Context, aux_id: usize, n: usize, f_set: &[i64]) {
    if f_set.is_empty() {
        ctx.emit("(assert false)");
    } else {
        let accept: Vec<String> = f_set
            .iter()
            .map(|&q| format!("_reg{aux_id}_{n}_{q}"))
            .collect();
        if accept.len() == 1 {
            ctx.emit_fmt(format_args!("(assert {})", accept[0]));
        } else {
            ctx.emit_fmt(format_args!("(assert (or {}))", accept.join(" ")));
        }
    }
}

#[cfg(test)]
mod emission_work_tests {
    use super::*;

    #[test]
    fn product_of_individually_bounded_dimensions_is_rejected() {
        let error = validate_emission_work(1_023, 1_024, 1_048_576)
            .expect_err("transition emission must be bounded before output");
        assert!(error.to_string().contains("encoding emits"), "{error}");
    }

    #[test]
    fn sink_transitions_do_not_consume_reaching_term_budget() {
        validate_emission_work(100, 100, 0).expect("small sink-only automaton should fit");
    }

    #[test]
    fn empty_sequence_skips_reverse_transition_materialization() {
        let mut ctx = Context::new();
        // The transition helper must return before scanning the table. This is
        // what keeps an empty regular sequence from allocating a Q*S reverse
        // index after the full constraint has already validated its table.
        regular_transitions(&mut ctx, 0, &[], usize::MAX, usize::MAX, &[]);
        assert!(ctx.output.is_empty());
    }
}
