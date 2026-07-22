// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, FxHashMap, FxHashSet, PdrSolver, PredicateId};

pub(super) fn entry_domain_constraint(
    solver: &PdrSolver,
    pred: PredicateId,
    level: usize,
) -> Option<ChcExpr> {
    if solver.predicate_has_facts(pred) {
        return None;
    }

    let canonical_vars = solver.canonical_vars(pred)?;
    let mut entry_constraints: Vec<ChcExpr> = Vec::new();

    for clause in solver.problem.clauses_defining(pred) {
        if clause.body.predicates.is_empty() || clause.body.predicates.len() != 1 {
            continue;
        }

        let (body_pred, body_args) = &clause.body.predicates[0];
        if *body_pred == pred {
            continue;
        }

        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, args) => args,
            crate::ClauseHead::False => continue,
        };

        let body_var_names: FxHashSet<String> = body_args
            .iter()
            .flat_map(|b| b.vars().into_iter().map(|v| v.name))
            .collect();
        let is_identity_like = head_args.len() == canonical_vars.len()
            && head_args.iter().all(|h_arg| {
                let vars = h_arg.vars();
                !vars.is_empty() && vars.iter().all(|v| body_var_names.contains(&v.name))
            });

        if !is_identity_like {
            continue;
        }

        let mut head_to_canonical: FxHashMap<String, String> = FxHashMap::default();
        for (h_arg, c_var) in head_args.iter().zip(canonical_vars.iter()) {
            match h_arg {
                ChcExpr::Var(hv) => {
                    head_to_canonical.insert(hv.name.clone(), c_var.name.clone());
                }
                expr => {
                    for v in expr.vars_of_sort(&c_var.sort) {
                        head_to_canonical
                            .entry(v.name.clone())
                            .or_insert_with(|| c_var.name.clone());
                    }
                }
            }
        }

        let mut conjuncts: Vec<ChcExpr> = Vec::new();
        if let Some(ref constraint) = clause.body.constraint {
            if !matches!(constraint, ChcExpr::Bool(true)) {
                let renamed = PdrSolver::rename_to_canonical_vars(constraint, &head_to_canonical);
                conjuncts.push(renamed);
            }
        }

        if let Some(frame) = solver.cumulative_frame_constraint(level, *body_pred) {
            if let Some(pred_canonical) = solver.canonical_vars(*body_pred) {
                let mut pred_to_head: FxHashMap<String, ChcExpr> = FxHashMap::default();
                for (body_arg, pred_canon) in body_args.iter().zip(pred_canonical.iter()) {
                    let vars_to_check: Vec<String> =
                        body_arg.vars().into_iter().map(|v| v.name).collect();
                    for var_name in vars_to_check {
                        if let Some(canon_name) = head_to_canonical.get(&var_name) {
                            let canon_var = canonical_vars
                                .iter()
                                .find(|v| &v.name == canon_name)
                                .cloned();
                            if let Some(cv) = canon_var {
                                pred_to_head.insert(pred_canon.name.clone(), ChcExpr::var(cv));
                                break;
                            }
                        }
                    }
                }
                let renamed_frame = frame.substitute_name_map(&pred_to_head);
                conjuncts.push(renamed_frame);
            }
        }

        if !conjuncts.is_empty() {
            entry_constraints.push(ChcExpr::and_all(conjuncts));
        }
    }

    match entry_constraints.len() {
        0 => None,
        1 => entry_constraints.into_iter().next(),
        _ => {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: entry_domain_constraint: pred {} has multiple entry clauses; skipping entry domain restriction",
                    pred.index()
                );
            }
            None
        }
    }
}
