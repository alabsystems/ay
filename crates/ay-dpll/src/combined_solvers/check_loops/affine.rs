// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;

use ay_core::term::{Constant, Symbol, TermData, TermStore};
use ay_core::TermId;
use num_bigint::BigInt;
use num_traits::Zero;

type AffineIntExpr = (BTreeMap<String, BigInt>, BigInt);

fn merge_affine_terms(
    lhs: &mut BTreeMap<String, BigInt>,
    rhs: BTreeMap<String, BigInt>,
    sign: i32,
) {
    for (symbol, coeff) in rhs {
        let signed = if sign >= 0 { coeff } else { -coeff };
        let entry = lhs.entry(symbol.clone()).or_insert_with(|| BigInt::from(0));
        *entry += signed;
        if *entry == BigInt::from(0) {
            lhs.remove(&symbol);
        }
    }
    // Postcondition: no zero-coefficient entries remain after merging.
    debug_assert!(
        lhs.values().all(|c| !c.is_zero()),
        "BUG: merge_affine_terms left zero-coefficient entries"
    );
}

fn scale_affine(expr: &mut AffineIntExpr, factor: &BigInt) {
    expr.1 *= factor;
    for coeff in expr.0.values_mut() {
        *coeff *= factor;
    }
    expr.0.retain(|_, coeff| *coeff != BigInt::from(0));
    // Postcondition: scaling by zero must zero-out all terms.
    debug_assert!(
        !factor.is_zero() || (expr.0.is_empty() && expr.1.is_zero()),
        "BUG: scale_affine by 0 left non-zero terms: {} vars, constant={}",
        expr.0.len(),
        expr.1
    );
    // Postcondition: no zero-coefficient entries survive (retain cleaned them).
    debug_assert!(
        expr.0.values().all(|c| !c.is_zero()),
        "BUG: scale_affine left zero-coefficient entries after retain"
    );
}

fn parse_affine_int_expr(terms: &TermStore, term: TermId) -> Option<AffineIntExpr> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some((BTreeMap::new(), n.clone())),
        TermData::Var(name, _) => {
            let mut vars = BTreeMap::new();
            vars.insert(name.clone(), BigInt::from(1));
            Some((vars, BigInt::from(0)))
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut vars = BTreeMap::new();
                let mut constant = BigInt::from(0);
                for &arg in args {
                    let (arg_vars, arg_const) = parse_affine_int_expr(terms, arg)?;
                    merge_affine_terms(&mut vars, arg_vars, 1);
                    constant += arg_const;
                }
                Some((vars, constant))
            }
            "-" if args.len() == 1 => {
                let mut expr = parse_affine_int_expr(terms, args[0])?;
                scale_affine(&mut expr, &BigInt::from(-1));
                Some(expr)
            }
            "-" if args.len() >= 2 => {
                let mut expr = parse_affine_int_expr(terms, args[0])?;
                for &arg in &args[1..] {
                    let (arg_vars, arg_const) = parse_affine_int_expr(terms, arg)?;
                    merge_affine_terms(&mut expr.0, arg_vars, -1);
                    expr.1 -= arg_const;
                }
                Some((expr.0, expr.1))
            }
            "*" => {
                let mut const_factor = BigInt::from(1);
                let mut non_constant: Option<AffineIntExpr> = None;
                for &arg in args {
                    let parsed = parse_affine_int_expr(terms, arg)?;
                    if parsed.0.is_empty() {
                        const_factor *= parsed.1;
                    } else if non_constant.is_none() {
                        non_constant = Some(parsed);
                    } else {
                        return None;
                    }
                }
                let mut expr = non_constant.unwrap_or((BTreeMap::new(), BigInt::from(1)));
                scale_affine(&mut expr, &const_factor);
                Some(expr)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Returns true if two arithmetic terms are provably distinct due to a
/// non-zero constant offset: same variable coefficients, different constant.
pub(super) fn distinct_by_affine_offset(terms: &TermStore, lhs: TermId, rhs: TermId) -> bool {
    let Some(lhs_expr) = parse_affine_int_expr(terms, lhs) else {
        return false;
    };
    let Some(rhs_expr) = parse_affine_int_expr(terms, rhs) else {
        return false;
    };
    let result = lhs_expr.0 == rhs_expr.0 && lhs_expr.1 != rhs_expr.1;
    // Self-comparison must never yield distinct: a term has offset 0 from itself.
    debug_assert!(
        lhs != rhs || !result,
        "BUG: distinct_by_affine_offset returned true for self-comparison ({lhs:?})"
    );
    result
}
