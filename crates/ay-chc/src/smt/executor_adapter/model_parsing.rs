// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model parsing helpers for the executor adapter.
//!
//! Converts ay-dpll Executor output (SMT-LIB model text) into `SmtValue` maps.

use crate::smt::types::SmtValue;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Parse an SMT-LIB model string into a FxHashMap<String, SmtValue>.
///
/// Handles the `(model ...)` wrapper and `(define-fun name () Sort value)` entries.
/// This is a best-effort parser -- unparseable entries are silently skipped.
///
/// `dt_ctor_names` is a set of known DT constructor names. When a `(define-fun ...)`
/// body contains an App whose name is in this set, the value is parsed as
/// `SmtValue::Datatype(ctor, fields)` instead of being dropped.
pub(crate) fn parse_model_into(
    model: &mut FxHashMap<String, SmtValue>,
    model_str: &str,
    dt_ctor_names: &FxHashSet<String>,
) {
    if model_str.is_empty() {
        return;
    }

    // Strip the `(model ...)` wrapper if present, since `ay_frontend::parse`
    // does not recognize `(model ...)` as a valid SMT-LIB command.
    let inner = model_str
        .trim()
        .strip_prefix("(model")
        .and_then(|s| s.trim().strip_suffix(')'))
        .unwrap_or(model_str);

    // Try to parse via ay-frontend for robust handling.
    // Wrap in set-logic so the parser accepts the define-fun commands.
    let parse_input = format!("(set-logic ALL)\n{inner}");
    let commands = match ay_frontend::parse(&parse_input) {
        Ok(cmds) => cmds,
        Err(_) => {
            // Fall back to string-based extraction for simple cases.
            parse_model_simple(model, model_str);
            return;
        }
    };

    for cmd in &commands {
        // DefineFun is a tuple variant: DefineFun(name, params, sort, body)
        if let ay_frontend::Command::DefineFun(name, params, _sort, body) = cmd {
            // Only extract 0-arity define-funs (constants, not functions).
            if !params.is_empty() {
                continue;
            }
            // Convert the body term to SmtValue.
            if let Some(value) = term_body_to_smt_value(body, dt_ctor_names) {
                model.insert(name.clone(), value);
            }
        }
    }
}

/// Convert a ay-frontend Term (from define-fun body) to SmtValue.
///
/// Handles scalar constants (Bool, Int, Real, BitVec), arithmetic negation/division,
/// array values (store chains, constant arrays), and DT constructor applications.
pub(crate) fn term_body_to_smt_value(
    term: &ay_frontend::Term,
    dt_ctor_names: &FxHashSet<String>,
) -> Option<SmtValue> {
    use ay_frontend::Constant;
    match term {
        ay_frontend::Term::Const(Constant::True) => Some(SmtValue::Bool(true)),
        ay_frontend::Term::Const(Constant::False) => Some(SmtValue::Bool(false)),
        ay_frontend::Term::Const(Constant::Numeral(s)) => match s.parse::<i128>() {
            Ok(n) => Some(SmtValue::Int(n)),
            // Phase-2 BigInt escape: beyond-i128 numerals become canonical
            // SmtValue::BigInt instead of being dropped from the model.
            Err(_) => match s.parse::<num_bigint::BigInt>() {
                Ok(n) => Some(SmtValue::int_from_bigint(n)),
                Err(_) => {
                    tracing::warn!(
                        "executor_adapter: unparseable numeral '{s}', dropping from model"
                    );
                    None
                }
            },
        },
        ay_frontend::Term::Const(Constant::Decimal(s)) => {
            parse_decimal_to_rational(s).map(SmtValue::Real)
        }
        ay_frontend::Term::Const(Constant::Hexadecimal(s)) => {
            // `ay_frontend` preserves the `#x` prefix in the literal (matching
            // the elaborator at ay-frontend/src/elaborate/term.rs:670); strip it
            // before parsing so the width and value are computed from the raw
            // hex digits, not the prefixed string.
            let hex = s.strip_prefix("#x").unwrap_or(s);
            let width = (hex.len() * 4) as u32;
            let val = if hex.len() > 32 {
                // Wide BV (>128-bit): truncate to low 128 bits.
                // The internal solver decomposes wide BV into ≤128-bit chunks,
                // so this only fires for executor fallback model values.
                let low = &hex[hex.len() - 32..];
                u128::from_str_radix(low, 16).unwrap_or(0)
            } else {
                u128::from_str_radix(hex, 16).ok()?
            };
            Some(SmtValue::BitVec(val, width))
        }
        ay_frontend::Term::Const(Constant::Binary(s)) => {
            // Strip the `#b` prefix (see the Hexadecimal arm above).
            let bin = s.strip_prefix("#b").unwrap_or(s);
            let width = bin.len() as u32;
            let val = if bin.len() > 128 {
                let low = &bin[bin.len() - 128..];
                u128::from_str_radix(low, 2).unwrap_or(0)
            } else {
                u128::from_str_radix(bin, 2).ok()?
            };
            Some(SmtValue::BitVec(val, width))
        }
        // Nullary constructor: App with empty args that matches a known ctor name.
        ay_frontend::Term::App(name, args)
            if args.is_empty() && dt_ctor_names.contains(name.as_str()) =>
        {
            Some(SmtValue::Datatype(name.clone(), vec![]))
        }
        ay_frontend::Term::App(name, args) => term_body_app_to_smt_value(name, args, dt_ctor_names),
        ay_frontend::Term::QualifiedApp(
            ay_frontend::QualifiedIdentifier::Symbol(name),
            _sort,
            args,
        ) => term_body_app_to_smt_value(name, args, dt_ctor_names),
        // Nullary constructor as bare symbol (parser produces Symbol for `Green` in
        // `(define-fun color () Color Green)`).
        ay_frontend::Term::Symbol(name) if dt_ctor_names.contains(name.as_str()) => {
            Some(SmtValue::Datatype(name.clone(), vec![]))
        }
        _ => None,
    }
}

/// Handle App-shaped terms: negation, division, store, const-array, DT constructors.
fn term_body_app_to_smt_value(
    name: &str,
    args: &[ay_frontend::Term],
    dt_ctor_names: &FxHashSet<String>,
) -> Option<SmtValue> {
    match name {
        "-" if args.len() == 1 => match term_body_to_smt_value(&args[0], dt_ctor_names)? {
            // Negate through BigInt: exact for every input, including
            // i128::MIN's magnitude (checked_neg used to drop it) and
            // beyond-i128 BigInt operands; int_from_bigint re-canonicalizes.
            SmtValue::Int(n) => Some(SmtValue::int_from_bigint(-num_bigint::BigInt::from(n))),
            SmtValue::BigInt(b) => Some(SmtValue::int_from_bigint(-b.as_ref().clone())),
            SmtValue::Real(r) => Some(SmtValue::Real(-r)),
            _ => None,
        },
        "/" if args.len() == 2 => term_body_rational_div(&args[0], &args[1], dt_ctor_names),
        "store" if args.len() == 3 => {
            term_body_array_store(&args[0], &args[1], &args[2], dt_ctor_names)
        }
        // QualifiedApp("const", ...) from the structured parser path
        "const" if args.len() == 1 => {
            let default = term_body_to_smt_value(&args[0], dt_ctor_names)?;
            Some(SmtValue::ConstArray(Box::new(default)))
        }
        _ if dt_ctor_names.contains(name) => {
            // DT constructor application: parse each field recursively.
            let fields: Vec<SmtValue> = args
                .iter()
                .filter_map(|a| term_body_to_smt_value(a, dt_ctor_names))
                .collect();
            if fields.len() == args.len() {
                Some(SmtValue::Datatype(name.to_string(), fields))
            } else {
                Some(SmtValue::Opaque(format!("({name} ...)")))
            }
        }
        _ => None,
    }
}

/// Parse `(/ num den)` as `SmtValue::Real`.
fn term_body_rational_div(
    num_term: &ay_frontend::Term,
    den_term: &ay_frontend::Term,
    dt_ctor_names: &FxHashSet<String>,
) -> Option<SmtValue> {
    use num_rational::BigRational;
    let num = match term_body_to_smt_value(num_term, dt_ctor_names)? {
        SmtValue::Int(n) => BigRational::from_integer(n.into()),
        SmtValue::Real(r) => r,
        _ => return None,
    };
    let den = match term_body_to_smt_value(den_term, dt_ctor_names)? {
        SmtValue::Int(n) => BigRational::from_integer(n.into()),
        SmtValue::Real(r) => r,
        _ => return None,
    };
    if den == BigRational::from_integer(0.into()) {
        return None;
    }
    Some(SmtValue::Real(num / den))
}

/// #6047: Parse `(store base idx val)` into `SmtValue::ArrayMap`.
fn term_body_array_store(
    base_term: &ay_frontend::Term,
    idx_term: &ay_frontend::Term,
    val_term: &ay_frontend::Term,
    dt_ctor_names: &FxHashSet<String>,
) -> Option<SmtValue> {
    let base = term_body_to_smt_value(base_term, dt_ctor_names)
        .unwrap_or_else(|| SmtValue::Opaque(format!("{base_term:?}")));
    let idx = term_body_to_smt_value(idx_term, dt_ctor_names)?;
    let val = term_body_to_smt_value(val_term, dt_ctor_names)?;
    let (default, mut entries): (Box<SmtValue>, Vec<(SmtValue, SmtValue)>) = match base {
        SmtValue::ConstArray(d) => (d, Vec::new()),
        SmtValue::ArrayMap { default, entries } => (default, entries),
        other => (Box::new(other), Vec::new()),
    };
    entries.push((idx, val));
    Some(SmtValue::ArrayMap { default, entries })
}

/// Parse a decimal string like "1.5" or "3.0" to BigRational.
pub(crate) fn parse_decimal_to_rational(s: &str) -> Option<num_rational::BigRational> {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    if let Some(dot_pos) = s.find('.') {
        let int_part = &s[..dot_pos];
        let frac_part = &s[dot_pos + 1..];
        let scale = frac_part.len() as u32;
        // Combine: "1.5" -> numerator = 15, denominator = 10
        let combined = format!("{int_part}{frac_part}");
        let numerator: BigInt = combined.parse().ok()?;
        let denominator = BigInt::from(10u64).pow(scale);
        Some(BigRational::new(numerator, denominator))
    } else {
        // No decimal point: treat as integer
        let n: BigInt = s.parse().ok()?;
        Some(BigRational::from_integer(n))
    }
}

/// Simple fallback model parser using string matching.
pub(crate) fn parse_model_simple(model: &mut FxHashMap<String, SmtValue>, model_str: &str) {
    for line in model_str.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with("(define-fun ") {
            continue;
        }
        // Simple heuristic: split on spaces and look for () pattern.
        let parts: Vec<&str> = trimmed.splitn(5, ' ').collect();
        if parts.len() < 5 {
            continue;
        }
        let name = parts[1].trim_start_matches('|').trim_end_matches('|');
        if parts[2] != "()" {
            continue;
        }
        let rest = &trimmed[trimmed.find("() ").unwrap_or(0) + 3..];
        if let Some(val) = parse_simple_value(rest) {
            model.insert(name.to_string(), val);
        }
    }
}

/// Parse a simple "SORT VALUE)" string into SmtValue.
pub(crate) fn parse_simple_value(s: &str) -> Option<SmtValue> {
    let s = s.trim().trim_end_matches(')').trim();
    if s.starts_with("Int ") {
        let val_str = s.strip_prefix("Int ")?.trim();
        if val_str.starts_with("(- ") {
            let inner = val_str.strip_prefix("(- ")?.trim_end_matches(')').trim();
            // Phase-2 BigInt escape: parse through BigInt and negate exactly
            // (also covers the i128::MIN magnitude that `-n` on i128 misses),
            // then re-canonicalize via int_from_bigint.
            match inner.parse::<num_bigint::BigInt>() {
                Ok(n) => Some(SmtValue::int_from_bigint(-n)),
                Err(_) => {
                    tracing::warn!(
                        "executor_adapter: unparseable numeral '-{inner}', dropping from model"
                    );
                    None
                }
            }
        } else {
            match val_str.parse::<i128>() {
                Ok(n) => Some(SmtValue::Int(n)),
                // Phase-2 BigInt escape for beyond-i128 numerals.
                Err(_) => match val_str.parse::<num_bigint::BigInt>() {
                    Ok(n) => Some(SmtValue::int_from_bigint(n)),
                    Err(_) => {
                        tracing::warn!(
                            "executor_adapter: unparseable numeral '{val_str}', dropping from model"
                        );
                        None
                    }
                },
            }
        }
    } else if s.starts_with("Bool ") {
        let val_str = s.strip_prefix("Bool ")?.trim();
        match val_str {
            "true" => Some(SmtValue::Bool(true)),
            "false" => Some(SmtValue::Bool(false)),
            _ => None,
        }
    } else {
        None
    }
}
