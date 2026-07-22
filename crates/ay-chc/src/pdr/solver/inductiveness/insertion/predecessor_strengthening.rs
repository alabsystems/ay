// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, FxHashMap, Lemma, PdrSolver, PredicateId, SmtResult};

pub(super) fn try_strengthen_predecessors_for_entry(
    solver: &mut PdrSolver,
    pred: PredicateId,
    equality: &ChcExpr,
    level: usize,
) -> bool {
    let target_level = level.min(solver.frames.len().saturating_sub(1)).max(1);
    let clauses: Vec<_> = solver.problem.clauses_defining(pred).cloned().collect();
    let canonical_vars = match solver.canonical_vars(pred) {
        Some(v) => v.to_vec(),
        None => return false,
    };
    let mut any_strengthened = false;

    if solver.config.verbose {
        safe_eprintln!(
            "PDR: try_strengthen_predecessors_for_entry: pred {} equality {} ({} clauses, canonical_vars: {:?})",
            pred.index(),
            equality,
            clauses.len(),
            canonical_vars.iter().map(|v| &v.name).collect::<Vec<_>>()
        );
    }

    for clause in &clauses {
        if solver.is_cancelled() {
            return false;
        }
        if clause.body.predicates.is_empty() || clause.body.predicates.len() != 1 {
            continue;
        }
        let (body_pred, body_args) = &clause.body.predicates[0];
        if *body_pred == pred {
            continue;
        }
        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => continue,
        };
        if head_args.len() != canonical_vars.len() {
            continue;
        }

        let pred_vars = match solver.canonical_vars(*body_pred) {
            Some(v) => v.to_vec(),
            None => continue,
        };
        if body_args.len() != pred_vars.len() {
            continue;
        }

        let mut body_var_to_pred_idx: FxHashMap<String, usize> = FxHashMap::default();
        for (idx, b_arg) in body_args.iter().enumerate() {
            if let ChcExpr::Var(bv) = b_arg {
                body_var_to_pred_idx.insert(bv.name.clone(), idx);
            }
        }

        let vars_in_eq: Vec<_> = equality.vars().into_iter().collect();
        let mut subst = Vec::new();
        let mut translation_ok = true;
        for var in &vars_in_eq {
            let canon_idx = canonical_vars.iter().position(|v| v.name == var.name);
            let Some(canon_idx) = canon_idx else {
                translation_ok = false;
                break;
            };
            let head_arg = &head_args[canon_idx];
            if let ChcExpr::Var(hv) = head_arg {
                if let Some(&body_idx) = body_var_to_pred_idx.get(&hv.name) {
                    subst.push((var.clone(), ChcExpr::var(pred_vars[body_idx].clone())));
                } else {
                    translation_ok = false;
                    break;
                }
            } else {
                translation_ok = false;
                break;
            }
        }
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: strengthen: clause body_pred={} body_args={:?} head_args={:?} translation_ok={} subst_len={}",
                body_pred.index(),
                body_args.iter().map(|a| format!("{a}")).collect::<Vec<_>>(),
                head_args.iter().map(|a| format!("{a}")).collect::<Vec<_>>(),
                translation_ok,
                subst.len()
            );
        }
        if !translation_ok || subst.is_empty() {
            continue;
        }

        let translated_eq = equality.substitute(&subst);
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: strengthen: translated_eq={} for body_pred={}",
                translated_eq,
                body_pred.index()
            );
        }

        let clause_constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));

        let guard_vars: Vec<_> = clause_constraint.vars().into_iter().collect();
        let mut guard_subst = Vec::new();
        let mut guard_ok = true;
        for var in &guard_vars {
            if let Some(&body_idx) = body_var_to_pred_idx.get(&var.name) {
                guard_subst.push((var.clone(), ChcExpr::var(pred_vars[body_idx].clone())));
            } else {
                guard_ok = false;
                break;
            }
        }

        let translated_guard = if guard_ok && !guard_subst.is_empty() {
            clause_constraint.substitute(&guard_subst)
        } else if matches!(clause_constraint, ChcExpr::Bool(true)) {
            continue;
        } else {
            ChcExpr::Bool(true)
        };

        let conditional = if matches!(translated_guard, ChcExpr::Bool(true)) {
            translated_eq.clone()
        } else {
            ChcExpr::or(
                ChcExpr::not(translated_guard.clone()),
                translated_eq.clone(),
            )
        };

        if solver.config.verbose {
            safe_eprintln!(
                "PDR: strengthen: conditional={} guard_ok={} translated_guard={}",
                conditional,
                guard_ok,
                translated_guard
            );
        }

        if solver.frames.len() > target_level
            && solver.frames[target_level].contains_lemma(*body_pred, &conditional)
        {
            continue;
        }

        let blocking = if matches!(translated_guard, ChcExpr::Bool(true)) {
            ChcExpr::not(translated_eq.clone())
        } else {
            ChcExpr::and(
                translated_guard.clone(),
                ChcExpr::not(translated_eq.clone()),
            )
        };
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: strengthen: checking self-inductiveness for pred {} with blocking={} has_facts={}",
                body_pred.index(),
                blocking,
                solver.predicate_has_facts(*body_pred)
            );
        }
        let passes = if solver.predicate_has_facts(*body_pred) {
            solver.is_self_inductive_blocking(&blocking, *body_pred)
        } else if let Some(ed) = solver.entry_domain_constraint(*body_pred, target_level) {
            solver.is_self_inductive_blocking_with_entry_domain(&blocking, *body_pred, Some(&ed))
        } else {
            solver.is_self_inductive_blocking(&blocking, *body_pred)
        };

        if !passes {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Guard-conditioned invariant NOT self-inductive for pred {}: {}",
                    body_pred.index(),
                    conditional
                );
            }
            continue;
        }

        let init_valid = if solver.predicate_has_facts(*body_pred) {
            solver.blocks_initial_states(*body_pred, &blocking)
        } else if let Some(ed) = solver.entry_domain_constraint(*body_pred, target_level) {
            let query = ChcExpr::and(ed, blocking.clone());
            solver.smt.reset();
            matches!(
                solver
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(200)),
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
            )
        } else {
            true
        };
        if !init_valid {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Guard-conditioned invariant NOT init-valid for pred {}: {}",
                    body_pred.index(),
                    conditional
                );
            }
            continue;
        }

        if solver.config.verbose {
            safe_eprintln!(
                "PDR: Adding guard-conditioned invariant to pred {}: {} (for entry to pred {})",
                body_pred.index(),
                conditional,
                pred.index()
            );
        }
        solver.add_lemma_to_frame(
            Lemma::new(*body_pred, conditional, target_level),
            target_level,
        );
        any_strengthened = true;
    }

    any_strengthened
}
