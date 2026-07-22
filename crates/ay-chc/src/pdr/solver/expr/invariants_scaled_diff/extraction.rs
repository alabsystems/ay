// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcOp, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    /// Extract multiplicative relationships from initial constraints.
    /// Returns `(var_name, coefficient, other_var_name)` tuples for patterns
    /// like `var = coeff * other`.
    pub(in crate::pdr::solver) fn extract_init_multiplicative_relations(
        &self,
        predicate: PredicateId,
    ) -> Vec<(String, i128, String)> {
        let mut relations = Vec::new();

        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v,
            None => return relations,
        };

        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            let constraint = match &fact.body.constraint {
                Some(c) => c,
                None => continue,
            };

            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if head_args.len() != canonical_vars.len() {
                continue;
            }

            let mut var_map: FxHashMap<String, String> = FxHashMap::default();
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                if let ChcExpr::Var(v) = arg {
                    var_map.insert(v.name.clone(), canon.name.clone());
                }
            }

            extract_mult_relations_from_expr(constraint, &var_map, &mut relations);
        }

        relations
    }
}

fn extract_mult_relations_from_expr(
    expr: &ChcExpr,
    var_map: &FxHashMap<String, String>,
    relations: &mut Vec<(String, i128, String)>,
) {
    match expr {
        ChcExpr::Op(ChcOp::And, exprs) => {
            for e in exprs {
                extract_mult_relations_from_expr(e, var_map, relations);
            }
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            let left = &args[0];
            let right = &args[1];
            if let ChcExpr::Var(v) = left.as_ref() {
                let canon_name = var_map
                    .get(&v.name)
                    .cloned()
                    .unwrap_or_else(|| v.name.clone());
                if let Some((coeff, other_name)) = extract_mul_pattern(right, var_map) {
                    relations.push((canon_name, coeff, other_name));
                }
            }
            if let ChcExpr::Var(v) = right.as_ref() {
                let canon_name = var_map
                    .get(&v.name)
                    .cloned()
                    .unwrap_or_else(|| v.name.clone());
                if let Some((coeff, other_name)) = extract_mul_pattern(left, var_map) {
                    relations.push((canon_name, coeff, other_name));
                }
            }
        }
        _ => {}
    }
}

fn extract_mul_pattern(
    expr: &ChcExpr,
    var_map: &FxHashMap<String, String>,
) -> Option<(i128, String)> {
    match expr {
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            let left = &args[0];
            let right = &args[1];
            if let (ChcExpr::Int(coeff), ChcExpr::Var(v)) = (left.as_ref(), right.as_ref()) {
                let canon = var_map
                    .get(&v.name)
                    .cloned()
                    .unwrap_or_else(|| v.name.clone());
                return Some((*coeff, canon));
            }
            if let (ChcExpr::Var(v), ChcExpr::Int(coeff)) = (left.as_ref(), right.as_ref()) {
                let canon = var_map
                    .get(&v.name)
                    .cloned()
                    .unwrap_or_else(|| v.name.clone());
                return Some((*coeff, canon));
            }
            None
        }
        _ => None,
    }
}
