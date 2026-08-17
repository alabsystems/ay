// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Line-oriented fallback for malformed or partial model output.

use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use super::super::types::Model;

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

pub(super) fn parse_model_str_legacy(model_str: &str) -> Model {
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

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::super::parse_model_str;

    #[test]
    fn parent_parser_recovers_complete_legacy_entries_after_sexp_failure() {
        let malformed = concat!(
            ")\n",
            "(define-fun i () Int (- 7))\n",
            "(define-fun r () Real (/ 3 2))\n",
            "(define-fun b () Bool true)\n",
            "(define-fun s () String \"legacy child\")\n",
            "(define-fun bv () (_ BitVec 8) #x2a)\n",
        );
        assert!(ay_frontend::sexp::parse_sexps(malformed).is_err());

        let model = parse_model_str(malformed);
        assert_eq!(model.int_val_i64("i"), Some(-7));
        assert_eq!(model.real_val_f64("r"), Some(1.5));
        assert_eq!(model.bool_val("b"), Some(true));
        assert_eq!(model.get_string("s"), Some("legacy child"));
        assert_eq!(model.bv_val("bv"), Some((BigInt::from(42), 8)));
    }
}
