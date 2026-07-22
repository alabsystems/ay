// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Filter out literals from conjuncts that semantically match the mono-var pattern.
pub(crate) fn filter_out_lit(
    conjuncts: &[ChcExpr],
    mono_var_pattern: &ChcExpr,
    pattern_var: &ChcVar,
) -> Option<Vec<ChcExpr>> {
    let mut matcher = SemanticMatcher::new();
    let pattern_vars = [pattern_var.clone()];
    let mut remaining = Vec::new();
    let mut found_match = false;

    for conjunct in conjuncts {
        if let Some((positive, _values)) =
            matcher.matches_signed(mono_var_pattern, &pattern_vars, conjunct)
        {
            if positive {
                found_match = true;
                continue;
            }
        }

        remaining.push(conjunct.clone());
    }

    if found_match {
        Some(remaining)
    } else {
        None
    }
}

/// Conjecture-specific wrapper around [`filter_out_lit`] with Z3-style equality retry.
pub(crate) fn filter_out_lit_with_eq_retry(
    conjuncts: &[ChcExpr],
    mono_var_pattern: &ChcExpr,
    pattern_var: &ChcVar,
) -> Option<Vec<ChcExpr>> {
    filter_out_lit(conjuncts, mono_var_pattern, pattern_var).or_else(|| {
        let (e1, e2) = match mono_var_pattern {
            ChcExpr::Op(ChcOp::Le | ChcOp::Ge, args) if args.len() == 2 => {
                (args[0].clone(), args[1].clone())
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                ChcExpr::Op(ChcOp::Gt | ChcOp::Lt, inner_args) if inner_args.len() == 2 => {
                    (inner_args[0].clone(), inner_args[1].clone())
                }
                _ => return None,
            },
            _ => return None,
        };

        let eq_pattern = ChcExpr::eq((*e1).clone(), (*e2).clone());
        filter_out_lit(conjuncts, &eq_pattern, pattern_var)
    })
}
