// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Search annotation parsing: FlatZinc int_search/bool_search/seq_search → ay-cp.
//!
//! Extracted from solve_cp/mod.rs to keep file sizes manageable.

use ay_cp::search::{SearchStrategy, ValueChoice};
use ay_cp::variable::IntVarId;
use ay_flatzinc_parser::ast::*;

use super::CpContext;

/// Apply FlatZinc search annotations to the CP engine.
///
/// Reads `int_search`/`bool_search` annotations and configures the engine's
/// variable selection strategy, value choice, and variable ordering.
/// Unknown annotations are silently ignored (the engine's defaults apply).
pub(super) fn apply_search_annotations(ctx: &mut CpContext, annotations: &[Annotation]) {
    for ann in annotations {
        if let Annotation::Call(name, args) = ann {
            match name.as_str() {
                "int_search" | "bool_search" => {
                    apply_search_annotation(ctx, args);
                }
                "seq_search" => {
                    // seq_search([search1, search2, ...]) — use the first
                    // search annotation for strategy. Collect all variable
                    // orderings for InputOrder.
                    if let Some(Expr::ArrayLit(elems)) = args.first() {
                        let mut all_vars = Vec::new();
                        let mut is_first = true;
                        for elem in elems {
                            if let Expr::Annotation(ann) = elem {
                                if let Annotation::Call(n, a) = ann.as_ref() {
                                    if n == "int_search" || n == "bool_search" {
                                        all_vars.extend(extract_search_vars(ctx, a));
                                        if is_first {
                                            apply_search_annotation(ctx, a);
                                            is_first = false;
                                        }
                                    }
                                }
                            }
                        }
                        if !all_vars.is_empty() {
                            ctx.engine.set_search_vars(all_vars);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

/// Apply a single int_search/bool_search annotation.
/// Args: [vars_array, var_choice, assign_choice, strategy].
fn apply_search_annotation(ctx: &mut CpContext, args: &[Expr]) {
    // Extract variable ordering
    let search_vars = extract_search_vars(ctx, args);
    if !search_vars.is_empty() {
        ctx.engine.set_search_vars(search_vars);
    }

    // Extract variable selection strategy (second argument)
    if let Some(Expr::Ident(strategy_name)) = args.get(1) {
        let strategy = match strategy_name.as_str() {
            "first_fail" => SearchStrategy::FirstFail,
            "dom_w_deg" => SearchStrategy::DomWDeg,
            "input_order" => SearchStrategy::InputOrder,
            "occurrence" => SearchStrategy::DomWDeg, // closest approximation
            "smallest" => SearchStrategy::FirstFail, // closest approximation
            _ => SearchStrategy::default(),
        };
        ctx.engine.set_search_strategy(strategy);
    }

    // Extract value selection strategy (third argument)
    if let Some(Expr::Ident(value_name)) = args.get(2) {
        let value_choice = match value_name.as_str() {
            "indomain_min" => ValueChoice::IndomainMin,
            "indomain_max" => ValueChoice::IndomainMax,
            "indomain_split" => ValueChoice::IndomainSplit,
            "indomain_reverse_split" => ValueChoice::IndomainReverseSplit,
            "indomain_median" => ValueChoice::IndomainSplit, // closest approximation
            _ => ValueChoice::default(),
        };
        ctx.engine.set_value_choice(value_choice);
    }
}

/// Extract variable IDs from the first argument of a search annotation.
fn extract_search_vars(ctx: &CpContext, args: &[Expr]) -> Vec<IntVarId> {
    let mut vars = Vec::new();
    if let Some(first) = args.first() {
        match first {
            Expr::ArrayLit(elems) => {
                for elem in elems {
                    if let Expr::Ident(name) = elem {
                        if let Some(&id) = ctx.var_map.get(name) {
                            vars.push(id);
                        } else if let Some(ids) = ctx.array_var_map.get(name) {
                            vars.extend(ids);
                        }
                    }
                }
            }
            Expr::Ident(name) => {
                if let Some(ids) = ctx.array_var_map.get(name) {
                    vars.extend(ids);
                } else if let Some(&id) = ctx.var_map.get(name) {
                    vars.push(id);
                }
            }
            _ => {}
        }
    }
    vars
}
