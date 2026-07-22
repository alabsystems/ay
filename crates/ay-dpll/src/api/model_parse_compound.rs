// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compound model value parsers: dispatching, sequences, arrays, FP, datatypes.
//!
//! Extracted from `model_parse.rs` for code health. Primitive parsers (int, real,
//! bool, BV) remain in `model_parse.rs`; this module handles compound types that
//! require recursive parsing or complex S-expression matching.

use ay_core::Sort;
use num_bigint::BigInt;

use super::model_parse::{
    parse_bv_value_with_width, parse_int_value_bigint, parse_real_value_bigrat,
};
use super::types::ModelValue;

/// Dispatch an S-expression to the appropriate type-specific parser based on sort.
pub(crate) fn parse_value_sexp(sexp: &ay_frontend::SExpr, sort: &Sort) -> ModelValue {
    match sort {
        Sort::Bool => match parse_bool_value(sexp) {
            Some(v) => ModelValue::Bool(v),
            None => ModelValue::Unknown,
        },
        Sort::Int => match parse_int_value_bigint(sexp) {
            Some(v) => ModelValue::Int(v),
            None => ModelValue::Unknown,
        },
        Sort::Real => match parse_real_value_bigrat(sexp) {
            Some(v) => ModelValue::Real(v),
            None => ModelValue::Unknown,
        },
        Sort::BitVec(bv) => match parse_bv_value(sexp) {
            Some(v) => ModelValue::BitVec {
                value: v,
                width: bv.width,
            },
            None => ModelValue::Unknown,
        },
        Sort::String => match sexp {
            ay_frontend::SExpr::String(s) => ModelValue::String(s.clone()),
            _ => ModelValue::Unknown,
        },
        Sort::Uninterpreted(_) => match sexp {
            ay_frontend::SExpr::Symbol(s) => ModelValue::Uninterpreted(s.clone()),
            _ => ModelValue::Uninterpreted(sexp.to_string()),
        },
        Sort::Array(arr) => parse_array_value(sexp, &arr.element_sort),
        Sort::FloatingPoint(eb, sb) => parse_fp_value(sexp, *eb, *sb),
        Sort::Datatype(_) => parse_dt_value(sexp, sort),
        Sort::RegLan => ModelValue::Unknown,
        Sort::Seq(elem_sort) => parse_seq_value(sexp, elem_sort),
        _ => ModelValue::Unknown,
    }
}

fn parse_bool_value(sexp: &ay_frontend::SExpr) -> Option<bool> {
    match sexp {
        ay_frontend::SExpr::True => Some(true),
        ay_frontend::SExpr::False => Some(false),
        _ => None,
    }
}

fn parse_bv_value(sexp: &ay_frontend::SExpr) -> Option<BigInt> {
    parse_bv_value_with_width(sexp).map(|(v, _)| v)
}

/// Parse a sequence value from an S-expression.
///
/// Handles these patterns:
/// - `seq.empty` or `(as seq.empty ...)` — empty sequence
/// - `(seq.unit <value>)` — singleton sequence
/// - `(seq.++ <s1> <s2>)` — concatenation (flattened recursively)
///
/// Falls back to `ModelValue::Unknown` for unrecognized patterns.
pub(super) fn parse_seq_value(sexp: &ay_frontend::SExpr, elem_sort: &Sort) -> ModelValue {
    match sexp {
        ay_frontend::SExpr::Symbol(s) if s == "seq.empty" => ModelValue::Seq(vec![]),
        ay_frontend::SExpr::List(items) => {
            if items.len() >= 2 {
                // Use is_symbol() instead of to_string() to avoid quoting issues
                // with reserved SMT-LIB words like "as" (quote_symbol returns "|as|").
                if items[0].is_symbol("as") && items.len() >= 2 && items[1].is_symbol("seq.empty") {
                    // (as seq.empty (Seq T)) — empty sequence
                    return ModelValue::Seq(vec![]);
                }
                if items[0].is_symbol("seq.unit") && items.len() == 2 {
                    // (seq.unit <value>)
                    let elem = parse_value_sexp(&items[1], elem_sort);
                    return ModelValue::Seq(vec![elem]);
                }
                if items[0].is_symbol("seq.++") && items.len() == 3 {
                    // (seq.++ <s1> <s2>) — flatten both sides
                    let left = parse_seq_value(&items[1], elem_sort);
                    let right = parse_seq_value(&items[2], elem_sort);
                    if let (ModelValue::Seq(mut l), ModelValue::Seq(r)) = (left, right) {
                        l.extend(r);
                        return ModelValue::Seq(l);
                    }
                }
            }
            ModelValue::Unknown
        }
        _ => ModelValue::Unknown,
    }
}

/// Parse a structured array value from an S-expression.
///
/// Handles these patterns:
/// - `((as const <sort>) <default>)` — constant array
/// - `(store <base> <index> <value>)` — store chain on top of base
///
/// Falls back to `ArraySmtlib(string)` if the structure is unrecognized.
pub(crate) fn parse_array_value(sexp: &ay_frontend::SExpr, element_sort: &Sort) -> ModelValue {
    // Collect stores from outermost to innermost, then find the base.
    let mut stores = Vec::new();
    let mut current = sexp;

    loop {
        match current.as_list() {
            Some(items) if items.len() == 4 && items[0].is_symbol("store") => {
                // (store <base> <index> <value>)
                let index = parse_value_for_array_elem(&items[2]);
                let value = parse_value_for_array_elem(&items[3]);
                stores.push((index, value));
                current = &items[1]; // descend into base
            }
            Some(items) if items.len() == 2 => {
                // ((as const <sort>) <default>) — 2-element list
                // The first element is itself a list: (as const <sort>)
                if let Some(inner) = items[0].as_list() {
                    if inner.len() >= 2 && inner[0].is_symbol("as") && inner[1].is_symbol("const") {
                        let default = parse_value_sexp(&items[1], element_sort);
                        stores.reverse(); // we collected outermost-first, want innermost-first
                        return ModelValue::Array {
                            default: Box::new(default),
                            stores,
                        };
                    }
                }
                // Unrecognized 2-element list — fall back
                break;
            }
            _ => break,
        }
    }

    // Fallback: return as raw string
    ModelValue::ArraySmtlib(sexp.to_string())
}

/// Parse a value from an array store index or value position.
///
/// Without full sort info, we infer the type from the S-expression syntax.
fn parse_value_for_array_elem(sexp: &ay_frontend::SExpr) -> ModelValue {
    match sexp {
        ay_frontend::SExpr::True => ModelValue::Bool(true),
        ay_frontend::SExpr::False => ModelValue::Bool(false),
        ay_frontend::SExpr::String(s) => ModelValue::String(s.clone()),
        ay_frontend::SExpr::Numeral(_) => match parse_int_value_bigint(sexp) {
            Some(v) => ModelValue::Int(v),
            None => ModelValue::Unknown,
        },
        ay_frontend::SExpr::Decimal(_) => match parse_real_value_bigrat(sexp) {
            Some(v) => ModelValue::Real(v),
            None => ModelValue::Unknown,
        },
        ay_frontend::SExpr::Hexadecimal(_) | ay_frontend::SExpr::Binary(_) => {
            match parse_bv_value_with_width(sexp) {
                Some((v, w)) => ModelValue::BitVec { value: v, width: w },
                None => ModelValue::Unknown,
            }
        }
        ay_frontend::SExpr::Symbol(s) => ModelValue::Uninterpreted(s.clone()),
        ay_frontend::SExpr::List(items) => {
            // Try: negative integer (- N)
            if items.len() == 2 && items[0].is_symbol("-") {
                if let Some(v) = parse_int_value_bigint(sexp) {
                    return ModelValue::Int(v);
                }
            }
            // Try: rational (/ N D)
            if items.len() == 3 && items[0].is_symbol("/") {
                if let Some(v) = parse_real_value_bigrat(sexp) {
                    return ModelValue::Real(v);
                }
            }
            ModelValue::Uninterpreted(sexp.to_string())
        }
        _ => ModelValue::Unknown,
    }
}

/// Parse an FP value: `(fp #b<sign> #b<exp> #b<sig>)` or `(_ +zero/NaN/+oo/-oo/-zero eb sb)`.
pub(crate) fn parse_fp_value(sexp: &ay_frontend::SExpr, eb: u32, sb: u32) -> ModelValue {
    use super::types::FpSpecialKind;

    let items = match sexp.as_list() {
        Some(items) => items,
        None => return ModelValue::Unknown,
    };

    if items.len() == 4 && items[0].is_symbol("_") {
        let kind = match items[1].as_symbol() {
            Some("+zero") => Some(FpSpecialKind::PosZero),
            Some("-zero") => Some(FpSpecialKind::NegZero),
            Some("+oo") => Some(FpSpecialKind::PosInf),
            Some("-oo") => Some(FpSpecialKind::NegInf),
            Some("NaN") => Some(FpSpecialKind::NaN),
            _ => None,
        };
        if let Some(kind) = kind {
            return ModelValue::FloatingPointSpecial { kind, eb, sb };
        }
    }

    if items.len() == 4 && items[0].is_symbol("fp") {
        let sign = match &items[1] {
            ay_frontend::SExpr::Binary(b) => {
                let bits = b.strip_prefix("#b").unwrap_or(b);
                bits == "1"
            }
            _ => return ModelValue::Unknown,
        };
        let exponent = match &items[2] {
            ay_frontend::SExpr::Binary(b) => {
                let bits = b.strip_prefix("#b").unwrap_or(b);
                u64::from_str_radix(bits, 2).ok()
            }
            _ => None,
        };
        let significand = match &items[3] {
            ay_frontend::SExpr::Binary(b) => {
                let bits = b.strip_prefix("#b").unwrap_or(b);
                u64::from_str_radix(bits, 2).ok()
            }
            _ => None,
        };
        if let (Some(exponent), Some(significand)) = (exponent, significand) {
            return ModelValue::FloatingPoint {
                sign,
                exponent,
                significand,
                eb,
                sb,
            };
        }
    }

    ModelValue::Unknown
}

/// Parse a datatype value: `ConstructorName` or `(Constructor arg1 arg2 ...)`.
///
/// Recursively parses nested compound types: DT args can themselves be
/// DT constructors, integers, booleans, bitvectors, reals, strings, etc.
pub(crate) fn parse_dt_value(sexp: &ay_frontend::SExpr, _sort: &Sort) -> ModelValue {
    match sexp {
        ay_frontend::SExpr::Symbol(name) => ModelValue::Datatype {
            constructor: name.clone(),
            args: Vec::new(),
        },
        ay_frontend::SExpr::List(items) if !items.is_empty() => {
            let constructor = match items[0].as_symbol() {
                Some(name) => name.to_string(),
                None => return ModelValue::Unknown,
            };
            let args = items[1..].iter().map(parse_dt_arg).collect();
            ModelValue::Datatype { constructor, args }
        }
        _ => ModelValue::Unknown,
    }
}

/// Parse a datatype constructor argument, inferring type from syntax.
///
/// Handles: Bool, Int (including negative), Real, BV (hex/binary), String,
/// and nested DT constructors `(Constructor arg1 ...)`.
fn parse_dt_arg(sexp: &ay_frontend::SExpr) -> ModelValue {
    match sexp {
        ay_frontend::SExpr::True => ModelValue::Bool(true),
        ay_frontend::SExpr::False => ModelValue::Bool(false),
        ay_frontend::SExpr::String(s) => ModelValue::String(s.clone()),
        ay_frontend::SExpr::Numeral(_) => match parse_int_value_bigint(sexp) {
            Some(v) => ModelValue::Int(v),
            None => ModelValue::Unknown,
        },
        ay_frontend::SExpr::Decimal(_) => match parse_real_value_bigrat(sexp) {
            Some(v) => ModelValue::Real(v),
            None => ModelValue::Unknown,
        },
        ay_frontend::SExpr::Hexadecimal(_) | ay_frontend::SExpr::Binary(_) => {
            match parse_bv_value_with_width(sexp) {
                Some((v, w)) => ModelValue::BitVec { value: v, width: w },
                None => ModelValue::Unknown,
            }
        }
        ay_frontend::SExpr::Symbol(s) => {
            // Could be a nullary DT constructor or an uninterpreted value.
            // Without sort info, treat as Uninterpreted (callers with sort
            // context can refine via parse_dt_value).
            ModelValue::Uninterpreted(s.clone())
        }
        ay_frontend::SExpr::List(items) if !items.is_empty() => {
            // Check for negative integer: (- N)
            if items.len() == 2 && items[0].is_symbol("-") {
                if let Some(v) = parse_int_value_bigint(sexp) {
                    return ModelValue::Int(v);
                }
            }
            // Check for rational: (/ N D)
            if items.len() == 3 && items[0].is_symbol("/") {
                if let Some(v) = parse_real_value_bigrat(sexp) {
                    return ModelValue::Real(v);
                }
            }
            // Nested DT constructor: (Constructor arg1 arg2 ...)
            if let Some(name) = items[0].as_symbol() {
                if name != "-" && name != "/" && name != "store" && name != "as" {
                    let args: Vec<ModelValue> = items[1..].iter().map(parse_dt_arg).collect();
                    return ModelValue::Datatype {
                        constructor: name.to_string(),
                        args,
                    };
                }
            }
            ModelValue::Uninterpreted(sexp.to_string())
        }
        _ => ModelValue::Unknown,
    }
}
