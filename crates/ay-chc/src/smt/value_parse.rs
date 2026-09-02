// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT model-value parsing helpers.

use super::types::SmtValue;
use ay_core::Sort;
use ay_frontend::SExpr;
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::Zero;

fn parse_symbolic_model_value(s: &str) -> Option<SmtValue> {
    let trimmed = s.trim();
    if trimmed
        .strip_prefix("@arr")
        .is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
    {
        return Some(SmtValue::Opaque(trimmed.to_owned()));
    }

    trimmed
        .rsplit_once("_(")
        .filter(|(name, suffix)| !name.is_empty() && !suffix.is_empty() && trimmed.ends_with(')'))
        .map(|(name, _)| SmtValue::Opaque(name.to_owned()))
}

/// Parse a string model value into an `SmtValue` based on the expected sort.
///
/// Returns `None` on parse failure with a warning logged to stderr. Proof and
/// witness callers must propagate that failure rather than inventing a value.
pub(super) fn parse_smt_value_str(s: &str, sort: &Sort) -> Option<SmtValue> {
    let trimmed = s.trim();
    match sort {
        Sort::Bool => match trimmed {
            "true" => Some(SmtValue::Bool(true)),
            "false" => Some(SmtValue::Bool(false)),
            _ => parse_symbolic_model_value(trimmed).or_else(|| {
                safe_eprintln!(
                    "[CHC-SMT] WARNING: parse_smt_value_str: \
                     unparseable Bool: {s:?}"
                );
                None
            }),
        },
        Sort::Int => {
            if let Ok(v) = trimmed.parse::<BigInt>() {
                Some(SmtValue::int_from_bigint(v))
            } else if let Some(inner) = trimmed
                .strip_prefix("(- ")
                .and_then(|s| s.strip_suffix(')'))
            {
                if let Ok(v) = inner.trim().parse::<BigInt>() {
                    Some(SmtValue::int_from_bigint(-v))
                } else if let Some(symbol) = parse_symbolic_model_value(trimmed) {
                    Some(symbol)
                } else {
                    safe_eprintln!(
                        "[CHC-SMT] WARNING: parse_smt_value_str: \
                         unparseable negative Int: {s:?}"
                    );
                    None
                }
            } else if let Some(symbol) = parse_symbolic_model_value(trimmed) {
                Some(symbol)
            } else {
                safe_eprintln!(
                    "[CHC-SMT] WARNING: parse_smt_value_str: \
                     unparseable Int: {s:?}"
                );
                None
            }
        }
        Sort::BitVec(bvs) => {
            if bvs.width == 0 || bvs.width > crate::MAX_BITVECTOR_WIDTH {
                safe_eprintln!(
                    "[CHC-SMT] WARNING: parse_smt_value_str: unsupported BV width {}",
                    bvs.width
                );
                return None;
            }
            let val = if let Some(hex) = trimmed.strip_prefix("#x") {
                match BigUint::parse_bytes(hex.as_bytes(), 16) {
                    Some(v) => v,
                    None => {
                        safe_eprintln!(
                            "[CHC-SMT] WARNING: parse_smt_value_str: \
                             unparseable BV hex: {s:?}"
                        );
                        return None;
                    }
                }
            } else if let Some(bin) = trimmed.strip_prefix("#b") {
                match BigUint::parse_bytes(bin.as_bytes(), 2) {
                    Some(v) => v,
                    None => {
                        safe_eprintln!(
                            "[CHC-SMT] WARNING: parse_smt_value_str: \
                             unparseable BV binary: {s:?}"
                        );
                        return None;
                    }
                }
            } else {
                match trimmed.parse::<BigUint>() {
                    Ok(v) => v,
                    Err(_) => {
                        return parse_symbolic_model_value(trimmed).or_else(|| {
                            safe_eprintln!(
                                "[CHC-SMT] WARNING: parse_smt_value_str: \
                                 unparseable BV decimal: {s:?}"
                            );
                            None
                        });
                    }
                }
            };
            Some(SmtValue::bitvec_from_biguint(val, bvs.width))
        }
        Sort::Real => parse_real_value(trimmed)
            .or_else(|| parse_symbolic_model_value(trimmed))
            .or_else(|| {
                safe_eprintln!(
                    "[CHC-SMT] WARNING: parse_smt_value_str: \
                     unparseable Real: {s:?}"
                );
                None
            }),
        _ => {
            safe_eprintln!(
                "[CHC-SMT] WARNING: parse_smt_value_str: \
                 unsupported sort {sort:?} for value {s:?}"
            );
            None
        }
    }
}

/// Parse an SMT-LIB Real value string into an `SmtValue::Real`.
///
/// Handles integer literals, decimals, `(- N)`, `(/ N D)`, and `(- (/ N D))`.
fn parse_real_value(s: &str) -> Option<SmtValue> {
    let trimmed = s.trim();
    if let Some(value) = parse_real_rational(trimmed) {
        return Some(SmtValue::Real(value));
    }

    safe_eprintln!(
        "[CHC-SMT] WARNING: parse_real_value: \
         unparseable Real: {s:?}"
    );
    None
}

fn parse_real_rational(s: &str) -> Option<BigRational> {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return None;
    }

    if let Ok(sexp) = ay_frontend::sexp::parse_sexp(trimmed) {
        if let Some(value) = parse_real_sexpr(&sexp) {
            return Some(value);
        }
    }

    parse_decimal_or_integer_rational(trimmed)
}

fn parse_real_sexpr(sexp: &SExpr) -> Option<BigRational> {
    match sexp {
        SExpr::Numeral(n) | SExpr::Symbol(n) => parse_decimal_or_integer_rational(n),
        SExpr::Decimal(d) => parse_decimal_or_integer_rational(d),
        SExpr::List(items) if items.len() == 2 => {
            if !matches!(items.first(), Some(SExpr::Symbol(op)) if op == "-") {
                return None;
            }
            parse_real_sexpr(&items[1]).map(|value| -value)
        }
        SExpr::List(items) if items.len() == 3 => {
            if !matches!(items.first(), Some(SExpr::Symbol(op)) if op == "/") {
                return None;
            }
            let numerator = parse_real_sexpr(&items[1])?;
            let denominator = parse_real_sexpr(&items[2])?;
            if denominator.is_zero() {
                return None;
            }
            Some(numerator / denominator)
        }
        _ => None,
    }
}

fn parse_decimal_or_integer_rational(s: &str) -> Option<BigRational> {
    let trimmed = s.trim();
    if trimmed.contains('.') {
        let (negative, unsigned) = trimmed
            .strip_prefix('-')
            .map_or((false, trimmed), |rest| (true, rest));
        let dot_pos = unsigned.find('.')?;
        let int_part = &unsigned[..dot_pos];
        let frac_part = &unsigned[dot_pos + 1..];
        if int_part.is_empty() || frac_part.is_empty() {
            return None;
        }
        let denom = BigInt::from(10i64).pow(frac_part.len() as u32);
        let digits = format!("{int_part}{frac_part}");
        if let Ok(mut numer) = digits.parse::<BigInt>() {
            if negative {
                numer = -numer;
            }
            return Some(BigRational::new(numer, denom));
        }
    }

    if let Ok(v) = trimmed.parse::<BigInt>() {
        return Some(BigRational::from_integer(v));
    }

    None
}

/// Provide a default `SmtValue` for a given sort.
#[cfg(test)]
pub(super) fn default_smt_value(sort: &Sort) -> SmtValue {
    match sort {
        Sort::Bool => SmtValue::Bool(false),
        Sort::Int => SmtValue::Int(0),
        Sort::BitVec(bvs) => SmtValue::bitvec_from_biguint(BigUint::zero(), bvs.width),
        Sort::Real => SmtValue::Real(BigRational::from_integer(BigInt::from(0i64))),
        _ => SmtValue::Int(0),
    }
}

#[cfg(test)]
#[path = "value_parse_tests.rs"]
mod tests;
