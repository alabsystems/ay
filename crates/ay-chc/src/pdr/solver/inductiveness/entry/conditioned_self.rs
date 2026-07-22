// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

pub(super) fn is_self_inductive_blocking_with_entry_domain(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
    entry_domain: Option<&ChcExpr>,
) -> bool {
    let entry_domain = match entry_domain {
        Some(d) => d,
        None => return solver.is_self_inductive_blocking(blocking_formula, predicate),
    };
    let lemma = ChcExpr::not(blocking_formula.clone());

    // Get canonical variables for mapping entry domain to clause variables
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
        // #2901: Check cancellation between SMT queries in clause loop.
        if solver.is_cancelled() {
            return false;
        }
        if clause.body.predicates.is_empty() {
            // Fact clause - init check is done separately
            continue;
        }

        // Only handle single-predicate self-loops
        if clause.body.predicates.len() != 1 {
            let has_self_loop = clause
                .body
                .predicates
                .iter()
                .any(|(bp, _)| *bp == predicate);
            if !has_self_loop {
                continue;
            }
            // Hyperedge with self-loop: be conservative
            return false;
        }

        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => continue,
        };

        let (body_pred, body_args) = &clause.body.predicates[0];
        if *body_pred != predicate {
            // Not a self-loop - skip
            continue;
        }

        let clause_constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));

        // blocking_on_head = blocking_formula applied to head (post-state)
        let blocking_on_head = match solver.apply_to_args(predicate, blocking_formula, head_args) {
            Some(e) => e,
            None => return false,
        };

        // lemma_on_body = lemma applied to body (pre-state)
        let lemma_on_body = match solver.apply_to_args(predicate, &lemma, body_args) {
            Some(e) => e,
            None => return false,
        };

        // entry_domain_on_body = entry domain applied to body (pre-state)
        // Build mapping from canonical vars to body args
        let mut canon_to_body: FxHashMap<String, ChcExpr> = FxHashMap::default();
        for (body_arg, canon) in body_args.iter().zip(canonical_vars.iter()) {
            canon_to_body.insert(canon.name.clone(), body_arg.clone());
        }
        let entry_domain_on_body = entry_domain.substitute_name_map(&canon_to_body);

        // Query: entry_domain_on_body /\ lemma_on_body /\ clause_constraint /\ blocking_on_head
        // Adding entry_domain restricts the pre-state to reachable states
        let query = solver.bound_int_vars(ChcExpr::and_all(vec![
            entry_domain_on_body,
            lemma_on_body,
            clause_constraint,
            blocking_on_head,
        ]));

        let simplified = query.propagate_equalities();
        if matches!(simplified, ChcExpr::Bool(false)) {
            // UNSAT - this clause is fine
            continue;
        }

        let (smt_result, _) = PdrSolver::check_sat_with_ite_case_split(
            &mut solver.smt,
            solver.config.verbose,
            &simplified,
        );

        match smt_result {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // Good - inductiveness holds for this transition
                continue;
            }
            SmtResult::Sat(_) => {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: is_self_inductive_blocking_with_entry_domain FAILED: lemma {} not inductive (entry domain: {})",
                        lemma, entry_domain
                    );
                }
                return false;
            }
            SmtResult::Unknown => {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: is_self_inductive_blocking_with_entry_domain UNKNOWN: lemma {}",
                        lemma
                    );
                }
                return false;
            }
        }
    }

    true
}
