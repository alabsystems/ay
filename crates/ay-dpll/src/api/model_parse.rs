// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model output parsing for AY Solver API.

use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use ay_core::{Sort, TermStore};

use super::types::{Model, ModelValue, Term};

/// Parse a define-fun line and extract (name, sort, value)
fn parse_define_fun(line: &str) -> Option<(String, String, String)> {
    // Format: (define-fun name () Sort value)
    let content = line
        .trim_start_matches("(define-fun ")
        .trim_end_matches(')');
    let mut parts = content.splitn(2, " () ");
    let name = parts.next()?.to_string();
    let rest = parts.next()?;

    // Find the value after an Int, Real, Bool, or `(_ BitVec N)` sort.
    let (sort, value) = if rest.starts_with("(_ ") {
        // Indexed sort like (_ BitVec 32)
        let sort_end = rest.find(')')? + 1;
        let sort = rest[..sort_end].to_string();
        let value = rest[sort_end..].trim().to_string();
        (sort, value)
    } else {
        // Simple sort
        let mut parts = rest.splitn(2, ' ');
        let sort = parts.next()?.to_string();
        let value = parts.next()?.trim().to_string();
        (sort, value)
    };

    Some((name, sort, value))
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ModelSort {
    Int,
    Real,
    Bool,
    BitVec(u32),
    Str,
    FloatingPoint(u32, u32),
    Seq(Box<Self>),
    Array(Box<Self>, Box<Self>),
    /// User-declared sort name (may be datatype or uninterpreted).
    /// Disambiguation happens at value-parse time.
    UserDeclared(String),
}

pub(super) fn parse_model_str(model_str: &str) -> Model {
    if let Ok(sexps) = ay_frontend::sexp::parse_sexps(model_str) {
        let mut model = Model {
            int_values: HashMap::default(),
            real_values: HashMap::default(),
            bool_values: HashMap::default(),
            bv_values: HashMap::default(),
            fp_values: HashMap::default(),
            string_values: HashMap::default(),
            seq_values: HashMap::default(),
            array_values: HashMap::default(),
            datatype_values: HashMap::default(),
            uninterpreted_values: HashMap::default(),
        };

        let mut define_funs = Vec::new();
        for sexp in &sexps {
            collect_define_funs(sexp, &mut define_funs);
        }

        for def in define_funs {
            if let Some((name, sort, value)) = parse_define_fun_sexp(def) {
                match sort {
                    ModelSort::Int => {
                        if let Some(v) = parse_int_value_bigint(value) {
                            model.int_values.insert(name, v);
                        }
                    }
                    ModelSort::Real => {
                        if let Some(v) = parse_real_value_bigrat(value) {
                            model.real_values.insert(name, v);
                        }
                    }
                    ModelSort::Bool => {
                        if let Some(v) = parse_bool_value(value) {
                            model.bool_values.insert(name, v);
                        }
                    }
                    ModelSort::BitVec(width) => {
                        if let Some(v) = parse_bv_value(value) {
                            model.bv_values.insert(name, (v, width));
                        }
                    }
                    ModelSort::Str => {
                        if let ay_frontend::SExpr::String(s) = value {
                            model.string_values.insert(name, s.clone());
                        }
                    }
                    ModelSort::FloatingPoint(eb, sb) => {
                        let v = parse_fp_value(value, eb, sb);
                        if v != ModelValue::Unknown {
                            model.fp_values.insert(name, v);
                        }
                    }
                    ModelSort::Seq(ref elem_sort) => {
                        let core_sort = model_sort_to_core(elem_sort);
                        let v = parse_seq_value(value, &core_sort);
                        if v != ModelValue::Unknown {
                            model.seq_values.insert(name, v);
                        }
                    }
                    ModelSort::Array(ref _idx, ref elem) => {
                        let elem_core = model_sort_to_core(elem);
                        let v = parse_array_value(value, &elem_core);
                        if v != ModelValue::Unknown {
                            model.array_values.insert(name, v);
                        }
                    }
                    ModelSort::UserDeclared(ref sort_name) => {
                        // The model printer sort-ascribes abstract elements of
                        // uninterpreted sorts so the output is valid SMT-LIB:
                        // `(as @S!0 S)`.  This list shape is not a datatype
                        // constructor application.  Preserve the bare element
                        // token in the uninterpreted-value map, which is the
                        // representation used by evaluation and universe
                        // reconstruction.  Restrict the special case to AY's
                        // `@...` abstract atoms and require the ascribed sort to
                        // match; datatype ascriptions such as `(as nil List)`
                        // must continue down the datatype path.
                        if let Some(element) = parse_ascribed_abstract_atom(value, sort_name) {
                            model.uninterpreted_values.insert(name, element);
                            continue;
                        }
                        // Bare symbols are ambiguous: could be nullary DT
                        // constructors OR uninterpreted sort elements. Without a
                        // sort registry we can't distinguish, so we conservatively
                        // treat bare symbols as uninterpreted (consumers can
                        // upgrade via sort info). Constructor *applications*
                        // (lists) are unambiguously DT values.
                        match value {
                            ay_frontend::SExpr::List(items) if !items.is_empty() => {
                                let core_sort = Sort::Datatype(ay_core::DatatypeSort {
                                    name: sort_name.clone(),
                                    constructors: Vec::new(),
                                });
                                let v = parse_dt_value(value, &core_sort);
                                if matches!(v, ModelValue::Datatype { .. }) {
                                    model.datatype_values.insert(name, v);
                                } else {
                                    model.uninterpreted_values.insert(name, value.to_string());
                                }
                            }
                            _ => {
                                let s = match value {
                                    ay_frontend::SExpr::Symbol(s) => s.clone(),
                                    other => other.to_string(),
                                };
                                model.uninterpreted_values.insert(name, s);
                            }
                        }
                    }
                }
            }
        }

        return model;
    }

    // Fallback: legacy line-based parser for malformed/partial model strings.
    parse_model_str_legacy(model_str)
}

/// Parse AY's printed abstract-element form `(as @S!n S)`.
///
/// The S-expression parser already removes pipe quoting, so this also covers
/// `(as |@foo::S!0| |foo::S|)` without a second textual unquoting path.
fn parse_ascribed_abstract_atom(value: &ay_frontend::SExpr, sort_name: &str) -> Option<String> {
    let items = value.as_list()?;
    let [head, element, ascribed_sort] = items else {
        return None;
    };
    if !head.is_symbol("as") || ascribed_sort.as_symbol()? != sort_name {
        return None;
    }
    let element = element.as_symbol()?;
    element.starts_with('@').then(|| element.to_string())
}

fn collect_define_funs<'a>(sexp: &'a ay_frontend::SExpr, out: &mut Vec<&'a ay_frontend::SExpr>) {
    let ay_frontend::SExpr::List(items) = sexp else {
        return;
    };

    if items
        .first()
        .is_some_and(|head| head.is_symbol("define-fun"))
    {
        out.push(sexp);
        // Don't recurse into define-fun bodies - they can't contain other define-funs
        return;
    }

    for item in items {
        collect_define_funs(item, out);
    }
}

fn parse_define_fun_sexp(
    sexp: &ay_frontend::SExpr,
) -> Option<(String, ModelSort, &ay_frontend::SExpr)> {
    let items = sexp.as_list()?;
    if items.len() != 5 || !items[0].is_symbol("define-fun") {
        return None;
    }

    let name = items[1].as_symbol()?.to_string();
    let params = items[2].as_list()?;
    if !params.is_empty() {
        // Only parse nullary define-fun entries into the Model for now.
        return None;
    }

    let sort = parse_model_sort(&items[3])?;
    Some((name, sort, &items[4]))
}

fn parse_model_sort(sexp: &ay_frontend::SExpr) -> Option<ModelSort> {
    match sexp {
        ay_frontend::SExpr::Symbol(s) if s == "Int" => Some(ModelSort::Int),
        ay_frontend::SExpr::Symbol(s) if s == "Real" => Some(ModelSort::Real),
        ay_frontend::SExpr::Symbol(s) if s == "Bool" => Some(ModelSort::Bool),
        ay_frontend::SExpr::Symbol(s) if s == "String" => Some(ModelSort::Str),
        // Unrecognized symbol: user-declared sort (datatype or uninterpreted)
        ay_frontend::SExpr::Symbol(s) => Some(ModelSort::UserDeclared(s.clone())),
        ay_frontend::SExpr::List(items) if items.len() == 3 => {
            // (_ BitVec N)
            if items[0].is_symbol("_") && items[1].is_symbol("BitVec") {
                match &items[2] {
                    ay_frontend::SExpr::Numeral(w) => w.parse::<u32>().ok().map(ModelSort::BitVec),
                    _ => None,
                }
            // (Array Index Elem)
            } else if items[0].is_symbol("Array") {
                let idx = parse_model_sort(&items[1])?;
                let elem = parse_model_sort(&items[2])?;
                Some(ModelSort::Array(Box::new(idx), Box::new(elem)))
            } else {
                None
            }
        }
        ay_frontend::SExpr::List(items) if items.len() == 4 => {
            // (_ FloatingPoint eb sb)
            if items[0].is_symbol("_") && items[1].is_symbol("FloatingPoint") {
                let eb = match &items[2] {
                    ay_frontend::SExpr::Numeral(n) => n.parse::<u32>().ok()?,
                    _ => return None,
                };
                let sb = match &items[3] {
                    ay_frontend::SExpr::Numeral(n) => n.parse::<u32>().ok()?,
                    _ => return None,
                };
                Some(ModelSort::FloatingPoint(eb, sb))
            } else {
                None
            }
        }
        ay_frontend::SExpr::List(items) if items.len() == 2 => {
            // (Seq T)
            if items[0].is_symbol("Seq") {
                let elem = parse_model_sort(&items[1])?;
                Some(ModelSort::Seq(Box::new(elem)))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Convert a `ModelSort` to a `ay_core::Sort` for use with `parse_seq_value`/`parse_fp_value`.
fn model_sort_to_core(sort: &ModelSort) -> Sort {
    match sort {
        ModelSort::Int => Sort::Int,
        ModelSort::Real => Sort::Real,
        ModelSort::Bool => Sort::Bool,
        ModelSort::BitVec(w) => Sort::BitVec(ay_core::BitVecSort::new(*w)),
        ModelSort::Str => Sort::String,
        ModelSort::FloatingPoint(eb, sb) => Sort::FloatingPoint(*eb, *sb),
        ModelSort::Seq(elem) => Sort::Seq(Box::new(model_sort_to_core(elem))),
        ModelSort::Array(idx, elem) => {
            Sort::array(model_sort_to_core(idx), model_sort_to_core(elem))
        }
        ModelSort::UserDeclared(name) => Sort::Uninterpreted(name.clone()),
    }
}

pub(super) fn parse_int_value_bigint(sexp: &ay_frontend::SExpr) -> Option<BigInt> {
    match sexp {
        ay_frontend::SExpr::Numeral(n) => BigInt::parse_bytes(n.as_bytes(), 10),
        ay_frontend::SExpr::Symbol(s) => BigInt::parse_bytes(s.as_bytes(), 10),
        ay_frontend::SExpr::List(items) if items.len() == 2 && items[0].is_symbol("-") => {
            parse_int_value_bigint(&items[1]).map(|v| -v)
        }
        _ => None,
    }
}

pub(super) fn parse_real_value_bigrat(sexp: &ay_frontend::SExpr) -> Option<BigRational> {
    match sexp {
        ay_frontend::SExpr::Numeral(_) | ay_frontend::SExpr::Symbol(_) => {
            let i = parse_int_value_bigint(sexp)?;
            Some(BigRational::from_integer(i))
        }
        ay_frontend::SExpr::Decimal(d) => {
            let f = d.parse::<f64>().ok()?;
            BigRational::from_float(f)
        }
        ay_frontend::SExpr::List(items) if items.len() == 2 && items[0].is_symbol("-") => {
            parse_real_value_bigrat(&items[1]).map(|v| -v)
        }
        ay_frontend::SExpr::List(items) if items.len() == 3 && items[0].is_symbol("/") => {
            // Operands recurse through the full Real grammar so the z3-exact
            // printed spelling `(/ 7.0 2.0)` parses too (#real-fmt); integer
            // operands behave exactly as before.
            let n = parse_real_value_bigrat(&items[1])?;
            let d = parse_real_value_bigrat(&items[2])?;
            if d.is_zero() {
                None
            } else {
                Some(n / d)
            }
        }
        _ => None,
    }
}

fn parse_bool_value(sexp: &ay_frontend::SExpr) -> Option<bool> {
    match sexp {
        ay_frontend::SExpr::True => Some(true),
        ay_frontend::SExpr::False => Some(false),
        _ => None,
    }
}

/// Parse a BV s-expression and infer the bit width from the representation.
/// Returns `(value, width)` or `None`.
pub(super) fn parse_bv_value_with_width(sexp: &ay_frontend::SExpr) -> Option<(BigInt, u32)> {
    match sexp {
        ay_frontend::SExpr::Hexadecimal(h) => {
            let hex = h.strip_prefix("#x").unwrap_or(h);
            let width = (hex.len() as u32) * 4;
            BigInt::parse_bytes(hex.as_bytes(), 16).map(|v| (v, width))
        }
        ay_frontend::SExpr::Binary(b) => {
            let bin = b.strip_prefix("#b").unwrap_or(b);
            let width = bin.len() as u32;
            BigInt::parse_bytes(bin.as_bytes(), 2).map(|v| (v, width))
        }
        ay_frontend::SExpr::List(items) if items.len() == 3 => {
            if items[0].is_symbol("_") {
                let ay_frontend::SExpr::Symbol(sym) = &items[1] else {
                    return None;
                };
                let value_str = sym.strip_prefix("bv")?;
                let ay_frontend::SExpr::Numeral(w) = &items[2] else {
                    return None;
                };
                let width = w.parse::<u32>().ok()?;
                return BigInt::parse_bytes(value_str.as_bytes(), 10).map(|v| (v, width));
            }
            None
        }
        _ => None,
    }
}

fn parse_bv_value(sexp: &ay_frontend::SExpr) -> Option<BigInt> {
    parse_bv_value_with_width(sexp).map(|(v, _)| v)
}

fn parse_legacy_int(value: &str) -> Option<BigInt> {
    if let Some(v) = BigInt::parse_bytes(value.as_bytes(), 10) {
        return Some(v);
    }
    if value.starts_with("(- ") {
        let inner = value.trim_start_matches("(- ").trim_end_matches(')');
        return BigInt::parse_bytes(inner.as_bytes(), 10).map(|v| -v);
    }
    None
}

fn parse_legacy_real(value: &str) -> Option<BigRational> {
    // Try integer first
    if let Some(v) = BigInt::parse_bytes(value.as_bytes(), 10) {
        return Some(BigRational::from_integer(v));
    }
    // Try decimal
    if let Ok(f) = value.parse::<f64>() {
        return BigRational::from_float(f);
    }
    if value.starts_with("(/ ") {
        let parts: Vec<&str> = value
            .trim_start_matches("(/ ")
            .trim_end_matches(')')
            .split_whitespace()
            .collect();
        if parts.len() == 2 {
            if let (Some(n), Some(d)) = (
                BigInt::parse_bytes(parts[0].as_bytes(), 10),
                BigInt::parse_bytes(parts[1].as_bytes(), 10),
            ) {
                if !d.is_zero() {
                    return Some(BigRational::new(n, d));
                }
            }
        }
    } else if value.starts_with("(- ") {
        let inner = value.trim_start_matches("(- ").trim_end_matches(')');
        return parse_legacy_real(inner).map(|v| -v);
    }
    None
}

fn parse_model_str_legacy(model_str: &str) -> Model {
    let mut model = Model {
        int_values: HashMap::default(),
        real_values: HashMap::default(),
        bool_values: HashMap::default(),
        bv_values: HashMap::default(),
        string_values: HashMap::default(),
        fp_values: HashMap::default(),
        seq_values: HashMap::default(),
        array_values: HashMap::default(),
        datatype_values: HashMap::default(),
        uninterpreted_values: HashMap::default(),
    };

    for line in model_str.lines() {
        let line = line.trim();
        if !line.starts_with("(define-fun ") {
            continue;
        }

        let Some((name, sort, value)) = parse_define_fun(line) else {
            continue;
        };

        match sort.as_str() {
            "Int" => {
                if let Some(v) = parse_legacy_int(&value) {
                    model.int_values.insert(name, v);
                }
            }
            "Real" => {
                if let Some(v) = parse_legacy_real(&value) {
                    model.real_values.insert(name, v);
                }
            }
            "Bool" => {
                model.bool_values.insert(name, value == "true");
            }
            "String" => {
                let stripped = value
                    .strip_prefix('"')
                    .and_then(|s| s.strip_suffix('"'))
                    .unwrap_or(&value);
                model.string_values.insert(name, stripped.to_string());
            }
            _ if sort.starts_with("(_ BitVec ") => {
                let width_str = sort.trim_start_matches("(_ BitVec ").trim_end_matches(')');
                if let Ok(width) = width_str.parse::<u32>() {
                    if let Some(binary) = value.strip_prefix("#b") {
                        if let Some(v) = BigInt::parse_bytes(binary.as_bytes(), 2) {
                            model.bv_values.insert(name, (v, width));
                        }
                    } else if let Some(hex) = value.strip_prefix("#x") {
                        if let Some(v) = BigInt::parse_bytes(hex.as_bytes(), 16) {
                            model.bv_values.insert(name, (v, width));
                        }
                    }
                }
            }
            _ => {}
        }
    }

    model
}

pub(super) fn parse_get_value_output(
    output: &str,
    terms: &[Term],
    term_store: &TermStore,
) -> Option<Vec<ModelValue>> {
    let sexps = ay_frontend::sexp::parse_sexps(output).ok()?;
    if sexps.len() != 1 {
        return None;
    }

    let pairs = sexps[0].as_list()?;
    if pairs.len() != terms.len() {
        return None;
    }

    let mut values = Vec::with_capacity(terms.len());
    for (pair, term) in pairs.iter().zip(terms.iter()) {
        let items = pair.as_list()?;
        if items.len() != 2 {
            return None;
        }

        let value_sexp = &items[1];
        // The caller authenticates the term slice; use its validated numeric ID.
        let sort = term_store.sort(term.id());
        values.push(parse_value_sexp(value_sexp, sort));
    }

    Some(values)
}

// Re-export compound parsers for backward compatibility with test imports.
use super::model_parse_compound::parse_seq_value;
pub(crate) use super::model_parse_compound::{
    parse_array_value, parse_dt_value, parse_fp_value, parse_value_sexp,
};
