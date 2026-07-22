// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, ChcOp, FxHashMap, Lemma, PdrSolver, PredicateId, SmtResult};

pub(super) fn retry_deferred_entry_invariants(solver: &mut PdrSolver) {
    if solver.deferred_entry_invariants.is_empty() {
        return;
    }
    let deferred = std::mem::take(&mut solver.deferred_entry_invariants);
    let mut still_deferred = Vec::new();
    for (pred, formula, level, retry_count) in deferred {
        if retry_count >= 3 {
            continue;
        }
        if solver.add_discovered_invariant_impl(pred, formula.clone(), level, false) {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Deferred entry-inductive retry SUCCEEDED for pred {}: {} (attempt {})",
                    pred.index(),
                    formula,
                    retry_count + 1
                );
            }
        } else {
            still_deferred.push((pred, formula, level, retry_count + 1));
        }
    }
    solver.deferred_entry_invariants = still_deferred;
}

pub(super) fn retry_deferred_self_inductive_invariants(solver: &mut PdrSolver) {
    if solver.deferred_self_inductive_invariants.is_empty() {
        return;
    }
    if solver.config.verbose {
        safe_eprintln!(
            "PDR: retry_deferred_self_inductive_invariants: {} deferred items",
            solver.deferred_self_inductive_invariants.len()
        );
    }
    let deferred = std::mem::take(&mut solver.deferred_self_inductive_invariants);
    let mut still_deferred = Vec::new();
    let mut added_any = false;

    for (pred, formula, level, retry_count) in &deferred {
        if *retry_count >= 3 {
            continue;
        }
        let frame_lemmas: Vec<ChcExpr> = solver
            .frames
            .get(*level)
            .map(|f| {
                f.lemmas
                    .iter()
                    .filter(|l| l.predicate == *pred && l.formula != *formula)
                    .map(|l| l.formula.clone())
                    .collect()
            })
            .unwrap_or_default();

        if frame_lemmas.is_empty() {
            continue;
        }

        let frame_conjunction = ChcExpr::and_all(frame_lemmas);
        if is_self_inductive_with_frame_context(solver, formula, *pred, &frame_conjunction) {
            let blocking = ChcExpr::not(formula.clone());
            let passes_entry = if solver.predicate_has_facts(*pred) {
                solver.blocks_initial_states(*pred, &blocking)
            } else {
                true
            };
            if passes_entry {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Deferred self-inductive retry SUCCEEDED for pred {}: {} (attempt {})",
                        pred.index(),
                        formula,
                        retry_count + 1
                    );
                }
                solver.rejected_invariants.remove(&(*pred, formula.clone()));
                solver.add_lemma_to_frame(Lemma::new(*pred, formula.clone(), *level), *level);
                added_any = true;
            }
        }
    }

    if !added_any {
        let mut by_pred: FxHashMap<PredicateId, Vec<(ChcExpr, usize)>> = FxHashMap::default();
        for (pred, formula, level, retry_count) in &deferred {
            if *retry_count < 3 {
                by_pred
                    .entry(*pred)
                    .or_default()
                    .push((formula.clone(), *level));
            }
        }

        for (pred, formulas) in &by_pred {
            if formulas.len() < 2 || solver.is_cancelled() {
                continue;
            }
            let level = formulas[0].1;

            let has_kernel_equalities = {
                let mut found = false;
                for lvl in 1..solver.frames.len() {
                    if let Some(f) = solver.frames.get(lvl) {
                        if f.lemmas.iter().any(|l| {
                            l.predicate == *pred
                                && l.algebraically_verified
                                && matches!(l.formula, ChcExpr::Op(ChcOp::Eq, _))
                        }) {
                            found = true;
                            break;
                        }
                    }
                }
                found
            };
            if has_kernel_equalities {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Skipping jointly-inductive retry for pred {} (kernel equalities already present)",
                        pred.index()
                    );
                }
                continue;
            }

            let all_formulas: Vec<ChcExpr> = formulas.iter().map(|(f, _)| f.clone()).collect();
            let mut all_pass = true;
            let mut passing_formulas: Vec<(ChcExpr, usize)> = Vec::new();
            for (i, (formula, lvl)) in formulas.iter().enumerate() {
                if solver.is_cancelled() {
                    all_pass = false;
                    break;
                }
                let mut context: Vec<ChcExpr> = all_formulas
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, f)| f.clone())
                    .collect();
                if let Some(f) = solver.frames.get(level) {
                    for l in &f.lemmas {
                        if l.predicate == *pred && !formulas.iter().any(|(ff, _)| ff == &l.formula)
                        {
                            context.push(l.formula.clone());
                        }
                    }
                }
                if context.is_empty() {
                    all_pass = false;
                    break;
                }
                let ctx = ChcExpr::and_all(context);
                if is_self_inductive_with_frame_context(solver, formula, *pred, &ctx) {
                    let blocking = ChcExpr::not(formula.clone());
                    let passes_entry = if solver.predicate_has_facts(*pred) {
                        solver.blocks_initial_states(*pred, &blocking)
                    } else {
                        true
                    };
                    if passes_entry {
                        passing_formulas.push((formula.clone(), *lvl));
                    } else {
                        all_pass = false;
                        break;
                    }
                } else {
                    all_pass = false;
                    break;
                }
            }
            if all_pass && !passing_formulas.is_empty() {
                for (formula, lvl) in passing_formulas {
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: Jointly-inductive group retry SUCCEEDED for pred {}: {}",
                            pred.index(),
                            formula
                        );
                    }
                    solver.rejected_invariants.remove(&(*pred, formula.clone()));
                    solver.add_lemma_to_frame(Lemma::new(*pred, formula.clone(), lvl), lvl);
                    added_any = true;
                }
            }
        }
    }

    if added_any {
        for (pred, formula, level, retry_count) in deferred {
            if retry_count >= 3 {
                continue;
            }
            if let Some(f) = solver.frames.get(level) {
                if f.contains_lemma(pred, &formula) {
                    continue;
                }
            }
            still_deferred.push((pred, formula, level, retry_count + 1));
        }
    } else {
        for (pred, formula, level, retry_count) in deferred {
            if retry_count >= 3 {
                continue;
            }
            still_deferred.push((pred, formula, level, retry_count + 1));
        }
    }
    solver.deferred_self_inductive_invariants = still_deferred;
}

pub(super) fn is_self_inductive_with_frame_context(
    solver: &mut PdrSolver,
    formula: &ChcExpr,
    predicate: PredicateId,
    frame_context: &ChcExpr,
) -> bool {
    let lemma = formula.clone();
    let blocking = ChcExpr::not(formula.clone());

    let canonical_vars = match solver.canonical_vars(predicate) {
        Some(v) => v.to_vec(),
        None => return false,
    };

    let clauses: Vec<_> = solver
        .problem
        .clauses_defining(predicate)
        .cloned()
        .collect();
    for clause in &clauses {
        if solver.is_cancelled() {
            return false;
        }
        if clause.body.predicates.is_empty() {
            continue;
        }
        if clause.body.predicates.len() != 1 {
            let has_self_loop = clause
                .body
                .predicates
                .iter()
                .any(|(bp, _)| *bp == predicate);
            if !has_self_loop {
                continue;
            }
            return false;
        }

        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => continue,
        };

        let (body_pred, body_args) = &clause.body.predicates[0];
        if *body_pred != predicate {
            continue;
        }

        let clause_constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));

        let blocking_on_head = match solver.apply_to_args(predicate, &blocking, head_args) {
            Some(e) => e,
            None => return false,
        };

        let lemma_on_body = match solver.apply_to_args(predicate, &lemma, body_args) {
            Some(e) => e,
            None => return false,
        };

        let mut canon_to_body: FxHashMap<String, ChcExpr> = FxHashMap::default();
        for (body_arg, canon) in body_args.iter().zip(canonical_vars.iter()) {
            canon_to_body.insert(canon.name.clone(), body_arg.clone());
        }
        let frame_on_body = frame_context.substitute_name_map(&canon_to_body);

        let query = solver.bound_int_vars(ChcExpr::and_all(vec![
            frame_on_body,
            lemma_on_body,
            clause_constraint,
            blocking_on_head,
        ]));

        // #8660 Phase 2: eagerly unfold `select(store(...))` via ROW axioms,
        // including the symbolic-index case (ITE form). Without this, the
        // ay-dpll array theory returns UNKNOWN on queries like
        // `select(store(a, i, v), 0) >= 42` where `i` is symbolic; Z3 Spacer
        // handles the equivalent via the array theory's eager case split on
        // `i = 0`. After this rewrite the query reduces to pure LIA+ITE, which
        // `check_sat_with_ite_case_split` can discharge.
        let row_expanded = query.expand_select_store_symbolic();
        let simplified = row_expanded.propagate_equalities();
        if matches!(simplified, ChcExpr::Bool(false)) {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: is_self_inductive_with_frame: {} for pred {} simplified to false (vacuously ok)",
                    formula,
                    predicate.index()
                );
            }
            continue;
        }

        let (smt_result, _) = PdrSolver::check_sat_with_ite_case_split(
            &mut solver.smt,
            solver.config.verbose,
            &simplified,
        );

        if solver.config.verbose {
            safe_eprintln!(
                "PDR: is_self_inductive_with_frame: {} for pred {}: smt={}",
                formula,
                predicate.index(),
                match &smt_result {
                    SmtResult::Sat(_) => "SAT(NOT inductive)",
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => "UNSAT(inductive)",
                    SmtResult::Unknown => "UNKNOWN",
                }
            );
        }

        match smt_result {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                continue;
            }
            SmtResult::Sat(ref model) => {
                let frame_epoch = solver.frames_lemma_epoch();
                super::super::super::core::record_validated_blocking_countermodel_from_head_args(
                    &mut solver.caches.implication_cache,
                    frame_epoch,
                    Some(canonical_vars.as_slice()),
                    predicate,
                    1,
                    head_args,
                    model,
                    &blocking,
                );
                return false;
            }
            _ => return false,
        }
    }
    true
}
